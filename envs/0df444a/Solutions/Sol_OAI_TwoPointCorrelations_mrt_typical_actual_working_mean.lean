-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_typical_actual_working_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:36:11.212846+00:00
-- url     : https://prove2.me/submissions/f559b6c5-53d8-41b6-945e-c80a480c4c6e

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_major_arc_corrected_typical_mean
import Theorems.Thm_OAI_TwoPointCorrelations_minor_arc_actual_working_mean
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_working_parameters

section
-- module Solutions.OAIChowla.OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds
namespace OAI
noncomputable section

open scoped _root_.BigOperators

namespace Problem337


instance goldbachSieveRootNonempty (u d : ℕ) : Nonempty (GoldbachSieveRoot u d) :=
  ⟨⟨0, by simp⟩⟩







end Problem337

end

end OAI

end

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

/-- Exact unit-cell decomposition, with no endpoint error. -/
theorem shortExponentialIntegral_eq_sum (b : ℕ → ℂ) (X D : ℕ) (α : ℝ) :
    shortExponentialIntegral b X D α =
      ∑ v ∈ range X, ‖shortExponentialSum b D α v‖ := by
  unfold shortExponentialIntegral
  symm
  calc
    _ = ∑ v ∈ range X, ∫ y in (v : ℝ)..((v + 1 : ℕ) : ℝ),
        ‖shortExponentialSum b D α y‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit b D α v).symm
    _ = _ := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => (n : ℝ)) (n := X)
          (fun v _ => by simpa only [Nat.cast_add, Nat.cast_one] using
            shortExponentialSum_unit_integrable b D α v))


lemma sum_Icc_shift (f : ℕ → ℂ) (v D : ℕ) :
    (∑ n ∈ Icc (v + 1) (v + D), f n) = ∑ m ∈ range D, f (v + m + 1) := by
  symm
  apply sum_bij (fun m _ => v + m + 1)
  · intro m hm
    simp only [mem_range] at hm
    simp only [mem_Icc]
    omega
  · intro m hm n hn he
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    refine ⟨n - (v + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega
  · intro m _
    rfl

lemma shortExponentialSum_at_nat (b : ℕ → ℂ) (D v : ℕ) (α : ℝ) :
    shortExponentialSum b D α v =
      ∑ n ∈ Icc (v + 1) (v + D), b n * additiveCharacter α n := by
  simp only [shortExponentialSum, Nat.floor_natCast,
    Nat.floor_add_natCast (Nat.cast_nonneg v) D]


lemma norm_additiveCharacter (α : ℝ) (n : ℕ) : ‖additiveCharacter α n‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcTrivial
namespace OAI

/-! The exact trivial bound used for bounded ranges of the short length. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma minor_arc_short_sum_trivial (F : ℕ → ℂ) (hF : OneBounded F)
    (H k : ℕ) (α : ℝ) : ‖shortExponentialSum F H α k‖ ≤ H := by
  rw [shortExponentialSum_at_nat]
  calc
    _ ≤ ∑ n ∈ Icc (k + 1) (k + H), ‖F n * additiveCharacter α n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc (k + 1) (k + H), (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, norm_additiveCharacter, mul_one]
      exact hF n (by have hh := (mem_Icc.mp hn).1; omega)
    _ = H := by
      simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      congr 1
      omega


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortSubdivision
namespace OAI

/-! Subdivision into fixed short lengths, retaining the additive
frequency and allowing all shifted origins in one enlarged prefix. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_short_sum_append (F : ℕ → ℂ) (a b v : ℕ) (α : ℝ) :
    shortExponentialSum F (a+b) α v =
      shortExponentialSum F a α v + shortExponentialSum F b α (v+a:ℕ) := by
  simp only [shortExponentialSum_at_nat, sum_Icc_shift]
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro n _
  simp only [Nat.add_assoc]

lemma mrt_short_sum_blocks (F : ℕ → ℂ) (h K v : ℕ) (α : ℝ) :
    shortExponentialSum F (K*h) α v =
      ∑ j ∈ range K, shortExponentialSum F h α (v+j*h:ℕ) := by
  induction K with
  | zero =>
    simp only [zero_mul, shortExponentialSum_at_nat, sum_Icc_shift, sum_range_zero]
  | succ K ih =>
    rw [show (K+1)*h = K*h+h by ring, mrt_short_sum_append, ih, sum_range_succ]

lemma mrt_short_subdivision_pointwise (F : ℕ → ℂ) (hF : OneBounded F)
    (H h v : ℕ) (hh : 0 < h) (α : ℝ) :
    ‖shortExponentialSum F H α v‖ ≤
      (∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(h:ℝ) := by
  have he : H = (H/h)*h+H%h := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod H h).symm
  have hs := mrt_short_sum_append F ((H/h)*h) (H%h) v α
  rw [← he] at hs
  have hsum : ‖∑ j ∈ range (H/h), shortExponentialSum F h α (v+j*h:ℕ)‖ ≤
      ∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖ :=
    norm_sum_le _ _
  have hrest₀ : ‖shortExponentialSum F (H%h) α (v+(H/h)*h:ℕ)‖ ≤ (H%h:ℕ) :=
    minor_arc_short_sum_trivial F hF (H%h) (v+(H/h)*h) α
  have hrest : ‖shortExponentialSum F (H%h) α (v+(H/h)*h:ℕ)‖ ≤ (h:ℝ) :=
    hrest₀.trans (by exact_mod_cast (Nat.mod_lt H hh).le)
  rw [hs, mrt_short_sum_blocks]
  exact (norm_add_le _ _).trans (add_le_add hsum hrest)


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcDivisorBounds
namespace OAI

/-! The divided-scale volume pays for the gcd sum. The main term costs
only sqrt(q)(1+log q), while endpoint rounding has an explicit q factor. -/

namespace TwoPointCorrelations

open _root_.Finset



lemma major_arc_log_overhead {W : ℝ} (hW : 1 ≤ W) :
    1+Real.log W ≤ 101*W^(1/100:ℝ) := by
  have hp : 1 ≤ W^(1/100:ℝ) := Real.one_le_rpow hW (by norm_num)
  have hl := Real.log_le_rpow_div (show 0 ≤ W by linarith) (show (0:ℝ) < 1/100 by norm_num)
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionParameters
namespace OAI

/-! Scalar budgets for the prime-power correction. The real parameter W
allows the published logarithmic cutoff, while the actual divisor cutoff
is the natural floor of W^5. -/

namespace TwoPointCorrelations

open scoped _root_.Classical




lemma mrt_correction_cutoff_bounds {W : ℝ} (hW : 2 ≤ W) :
    1 ≤ mrtCorrectionCutoff W ∧
      W ^ (5 : ℕ) / 2 ≤ (mrtCorrectionCutoff W : ℝ) ∧
      (mrtCorrectionCutoff W : ℝ) ≤ W ^ (5 : ℕ) := by
  have hW1 : 1 ≤ W := by linarith
  have hpow : 2 ≤ W ^ (5 : ℕ) :=
    hW.trans (le_self_pow₀ hW1 (by norm_num : (5 : ℕ) ≠ 0))
  have hlt := Nat.lt_floor_add_one (W ^ (5 : ℕ))
  refine ⟨?_, ?_, Nat.floor_le (pow_nonneg (by linarith) _)⟩
  · exact (Nat.one_le_floor_iff _).mpr (by linarith)
  · change W ^ (5 : ℕ) / 2 ≤ (⌊W ^ (5 : ℕ)⌋₊ : ℝ)
    linarith



lemma mrt_correction_quotient_length {W H : ℝ} {h d : ℕ}
    (hW : 0 < W) (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    H / W ^ (7 : ℕ) ≤ (h / d + 1 : ℕ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hquot : (h : ℝ) / d < (h / d + 1 : ℕ) := by
    apply (div_lt_iff₀ hdr).mpr
    have ht : (h : ℝ) < (d : ℝ) * (h / d + 1 : ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ h hd
    simpa only [mul_comm] using ht
  calc
    H / W ^ (7 : ℕ) = (H / W ^ (2 : ℕ)) / W ^ (5 : ℕ) := by
      rw [div_div, ← pow_add]
    _ ≤ (h : ℝ) / W ^ (5 : ℕ) := div_le_div_of_nonneg_right hh (pow_nonneg hW.le _)
    _ ≤ (h : ℝ) / d := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hdr hdW
    _ ≤ _ := hquot.le

lemma mrt_correction_quotient_power {W H : ℝ} {h d : ℕ}
    (hW : 1 ≤ W) (hH : W ^ (250 : ℕ) ≤ H)
    (hd : 0 < d) (hdW : (d : ℝ) ≤ W ^ (5 : ℕ))
    (hh : H / W ^ (2 : ℕ) ≤ (h : ℝ)) :
    W ^ (243 : ℕ) ≤ (h / d + 1 : ℕ) := by
  have hW0 : 0 < W := by linarith
  calc
    W ^ (243 : ℕ) = W ^ (250 : ℕ) / W ^ (7 : ℕ) := by
      rw [show (250 : ℕ) = 243 + 7 by decide, pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H / W ^ (7 : ℕ) := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_correction_quotient_length hW0 hd hdW hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcSubdivision
namespace OAI

/-! Subdivide before applying the major-arc perturbation estimate. The
chosen length keeps the phase variation bounded and still satisfies the
lower length required by the small-divisor correction. -/

namespace TwoPointCorrelations


lemma mrt_arc_subdivision_bounds {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) :
    0 < mrtArcSubdivisionLength H W ∧ mrtArcSubdivisionLength H W ≤ H ∧
      (H : ℝ) / W ^ (2 : ℕ) ≤ (mrtArcSubdivisionLength H W : ℝ) ∧
      (mrtArcSubdivisionLength H W : ℝ) ≤ (H : ℝ) / W := by
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hH0 : (0 : ℝ) < H := (pow_pos hW0 250).trans_le hH
  have hp : W ^ (2 : ℕ) ≤ (H : ℝ) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (2 : ℕ) ≤ 250)).trans hH
  have hWsq : 2 * W ≤ W ^ (2 : ℕ) := by nlinarith
  have htwo : (2 : ℝ) ≤ (H : ℝ) / W :=
    (le_div_iff₀ hW0).mpr (hWsq.trans hp)
  have hfloor := Nat.lt_floor_add_one ((H : ℝ) / W)
  have hlow : ((H : ℝ) / W) / 2 ≤ (mrtArcSubdivisionLength H W : ℝ) := by
    change (H : ℝ) / W / 2 ≤ (⌊(H : ℝ) / W⌋₊ : ℝ)
    linarith
  have hupper : (mrtArcSubdivisionLength H W : ℝ) ≤ (H : ℝ) / W :=
    Nat.floor_le (div_nonneg hH0.le hW0.le)
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_, hupper⟩
  · have hh := hupper.trans (div_le_self hH0.le hW1)
    exact_mod_cast hh
  · calc
      _ ≤ (H : ℝ) / (2 * W) :=
        div_le_div_of_nonneg_left hH0.le (by positivity) hWsq
      _ = ((H : ℝ) / W) / 2 := by ring
      _ ≤ _ := hlow

lemma mrt_arc_subdivision_remainder {H : ℕ} {W : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) :
    (mrtArcSubdivisionLength H W : ℝ) / H ≤ W ^ (-(1 / 4 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have hH0 : (0 : ℝ) < H := (pow_pos hW0 250).trans_le hH
  have hupper := (mrt_arc_subdivision_bounds hW hH).2.2.2
  calc
    _ ≤ ((H : ℝ) / W) / H := div_le_div_of_nonneg_right hupper hH0.le
    _ = W ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; field_simp
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

lemma mrt_arc_subdivision_phase {H q : ℕ} {W β : ℝ}
    (hW : 2 ≤ W) (hH : W ^ (250 : ℕ) ≤ (H : ℝ)) (hq : 0 < q)
    (hβ : |β| ≤ W / ((H : ℝ) * q)) :
    |β| * (mrtArcSubdivisionLength H W : ℝ) ≤ 1 / (q : ℝ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : (0 : ℝ) < H := (pow_pos hW0 250).trans_le hH
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hh := (mrt_arc_subdivision_bounds hW hH).2.2.2
  calc
    _ ≤ (W / ((H : ℝ) * q)) * ((H : ℝ) / W) :=
      mul_le_mul hβ hh (Nat.cast_nonneg _) (by positivity)
    _ = _ := by field_simp


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcQuotientScale
namespace OAI

/-! The correction divisor and the gcd divisor together cost at most
W^6. These bounds retain the actual floor quotients after subdivision. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma mrt_arc_combined_divisor {W : ℝ} {d b : ℕ}
    (hW : 0 ≤ W) (hd : (d : ℝ) ≤ W ^ (5 : ℕ)) (hb : (b : ℝ) ≤ W) :
    ((d * b : ℕ) : ℝ) ≤ W ^ (6 : ℕ) := by
  push_cast
  calc
    (d : ℝ) * b ≤ W ^ (5 : ℕ) * W :=
      mul_le_mul hd hb (Nat.cast_nonneg b) (pow_nonneg hW _)
    _ = _ := by ring










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTArcRate
namespace OAI

/-! Scalar rates for a square-root modulus loss and the elementary
q^(1/100) divisor bound. These estimates do not assume or prove the
analytic character-resolution inequality. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma mrt_sqrt_modulus_power {W : ℝ} (hW : 0 < W) :
    Real.sqrt W * W ^ (1 / 100 : ℝ) = W ^ (51 / 100 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hW]
  norm_num










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcPublishedRate
namespace OAI

/-! The common major/minor-arc parameter and its quantitative rates.
The fifth-root working length retains the published logarithmic error. -/
namespace TwoPointCorrelations

open _root_.Filter


lemma major_arc_parameter_bounds {L H M : ℝ} (hL : 1 ≤ L)
    (hH : 1 ≤ Real.log H) (hM : 0 ≤ M) :
    1 ≤ majorArcParameter L H M ∧
      majorArcParameter L H M ≤ (Real.log H)^5 ∧
      majorArcParameter L H M ≤ L^(1/125:ℝ) ∧
      majorArcParameter L H M ≤ Real.exp (M/3) := by
  exact ⟨le_min (one_le_pow₀ hH) (le_min
    (Real.one_le_rpow hL (by norm_num)) (Real.one_le_exp (by positivity))),
    min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩


lemma major_arc_working_short {H : ℝ} (hH : 1 ≤ Real.log H)
    (hHH : 1 ≤ Real.log (Real.log H)) :
    majorArcWorkingError ((Real.log H)^5) ≤ 6*Real.log (Real.log H)/Real.log H := by
  have hL : 0 < Real.log H := by linarith
  have hp : ((Real.log H)^5)^(-1/5:ℝ) = (Real.log H)⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num [Real.rpow_neg_one]
  unfold majorArcWorkingError
  rw [hp,Real.log_pow]
  rw [mul_inv_le_iff₀ hL]
  field_simp
  norm_num
  linarith

lemma major_arc_working_exponential {M : ℝ} (hM : 0 ≤ M) :
    majorArcWorkingError (Real.exp (M/3)) ≤ 21*Real.exp (-M/20) := by
  have hh := Real.add_one_le_exp (M/60)
  have hcoef : 1+M/3 ≤ 21*Real.exp (M/60) := by
    have he : 1 ≤ Real.exp (M/60) := Real.one_le_exp (by positivity)
    linarith
  unfold majorArcWorkingError
  rw [Real.log_exp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  calc
    _ ≤ (21*Real.exp (M/60))*Real.exp (M/3*(-1/5)) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

lemma major_arc_working_outer :
    ∀ᶠ L : ℝ in atTop,
      majorArcWorkingError (L^(1/125:ℝ)) ≤ L^(-1/700:ℝ) := by
  have hh := (isLittleO_log_rpow_atTop (show (0:ℝ)<3/17500 by norm_num)).bound
    (show (0:ℝ)<1/2 by norm_num)
  have hg := (tendsto_rpow_atTop (show (0:ℝ)<3/17500 by norm_num)).eventually
    (eventually_ge_atTop (2:ℝ))
  filter_upwards [hh,hg,eventually_ge_atTop (1:ℝ)] with L hh hg hL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hh
  have hp : (L^(1/125:ℝ))^(-1/5:ℝ)=L^(-1/625:ℝ) := by
    rw [← Real.rpow_mul hL0.le]
    norm_num
  unfold majorArcWorkingError
  rw [Real.log_rpow hL0,hp]
  calc
    _ ≤ L^(3/17500:ℝ)*L^(-1/625:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0.le _)
      nlinarith [Real.log_nonneg hL]
    _ = _ := by rw [← Real.rpow_add hL0]; norm_num

lemma major_arc_working_min {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    majorArcWorkingError (min a b) ≤ majorArcWorkingError a+majorArcWorkingError b := by
  have hfa : 0 ≤ majorArcWorkingError a :=
    mul_nonneg (by linarith [Real.log_nonneg ha]) (Real.rpow_nonneg (by linarith) _)
  have hfb : 0 ≤ majorArcWorkingError b :=
    mul_nonneg (by linarith [Real.log_nonneg hb]) (Real.rpow_nonneg (by linarith) _)
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact le_add_of_nonneg_right hfb
  · rw [min_eq_right hba]
    exact le_add_of_nonneg_left hfa

lemma major_arc_parameter_rate :
    ∀ᶠ L : ℝ in atTop, ∀ H M : ℝ, 1 ≤ Real.log H →
      1 ≤ Real.log (Real.log H) → 0 ≤ M →
      majorArcWorkingError (majorArcParameter L H M) ≤
        6*Real.log (Real.log H)/Real.log H + L^(-1/700:ℝ)+21*Real.exp (-M/20) := by
  filter_upwards [major_arc_working_outer,eventually_ge_atTop (1:ℝ)] with L houter hL
  intro H M hH hHH hM
  have ha : 1 ≤ (Real.log H)^5 := one_le_pow₀ hH
  have hb : 1 ≤ L^(1/125:ℝ) := Real.one_le_rpow hL (by norm_num)
  have hc : 1 ≤ Real.exp (M/3) := Real.one_le_exp (by positivity)
  have hi := major_arc_working_min hb hc
  have hj := major_arc_working_min ha (le_min hb hc)
  change majorArcWorkingError (majorArcParameter L H M) ≤ _ at hj
  linarith [major_arc_working_short hH hHH,major_arc_working_exponential hM]

theorem major_arc_sharp_energy_rate :
    ∀ᶠ L : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ L^(1/125:ℝ) →
      Real.sqrt W*(1+Real.log W)*Real.sqrt (Real.log L/L^(1/80:ℝ)) ≤
        101*L^(-1/700:ℝ) := by
  have hs := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/1000 by norm_num)).bound
    (show (0:ℝ)<1 by norm_num)
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with L hs hL
  have hL0 : 0 < L := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hL),Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL0.le _),one_mul] at hs
  intro W hW hWL
  have hW0 : 0 < W := by linarith
  have hmod : Real.sqrt W*W^(1/100:ℝ) ≤ L^(51/12500:ℝ) := by
    rw [mrt_sqrt_modulus_power hW0]
    calc
      _ ≤ (L^(1/125:ℝ))^(51/100:ℝ) := Real.rpow_le_rpow hW0.le hWL (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hL0.le]; norm_num
  have hratio : Real.log L/L^(1/80:ℝ) ≤ L^(-23/2000:ℝ) := by
    calc
      _ ≤ L^(1/1000:ℝ)/L^(1/80:ℝ) := div_le_div_of_nonneg_right hs (by positivity)
      _ = _ := by rw [← Real.rpow_sub hL0]; norm_num
  have hroot : Real.sqrt (Real.log L/L^(1/80:ℝ)) ≤ L^(-23/4000:ℝ) := by
    calc
      _ ≤ Real.sqrt (L^(-23/2000:ℝ)) := Real.sqrt_le_sqrt hratio
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul hL0.le]; norm_num
  calc
    _ ≤ Real.sqrt W*(101*W^(1/100:ℝ))*Real.sqrt (Real.log L/L^(1/80:ℝ)) := by
      gcongr
      exact major_arc_log_overhead hW
    _ = 101*((Real.sqrt W*W^(1/100:ℝ))*Real.sqrt (Real.log L/L^(1/80:ℝ))) := by ring
    _ ≤ 101*(L^(51/12500:ℝ)*L^(-23/4000:ℝ)) := by
      gcongr
    _ = 101*L^(-167/100000:ℝ) := by rw [← Real.rpow_add hL0]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)) (by norm_num)

lemma major_arc_sharp_distance_rate {W M : ℝ} (hW : 1 ≤ W) (hM : 0 ≤ M)
    (hWM : W ≤ Real.exp (M/3)) :
    Real.sqrt W*(1+Real.log W)*Real.exp (-2*M/5) ≤ 101*Real.exp (-M/20) := by
  have hW0 : 0 < W := by linarith
  calc
    _ ≤ Real.sqrt W*(101*W^(1/100:ℝ))*Real.exp (-2*M/5) := by
      gcongr
      exact major_arc_log_overhead hW
    _ = 101*(W^(51/100:ℝ)*Real.exp (-2*M/5)) := by
      rw [← mrt_sqrt_modulus_power hW0]
      ring
    _ ≤ 101*((Real.exp (M/3))^(51/100:ℝ)*Real.exp (-2*M/5)) := by
      gcongr
    _ = 101*Real.exp (-23*M/100) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hM])) (by norm_num)


lemma major_arc_inverse_working_rate {W : ℝ} (hW : 1 ≤ W) :
    Real.sqrt W*(1+Real.log W)*W⁻¹ ≤ majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  calc
    _ = (1+Real.log W)*W^(-1/2:ℝ) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_neg_one W]
      calc
        _ = (1+Real.log W)*(W^(1/2:ℝ)*W^(-1:ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hW0]; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hW (by norm_num))
      (by linarith [Real.log_nonneg hW])

theorem major_arc_weighted_energy_rate :
    ∀ᶠ L : ℝ in atTop, ∀ W M : ℝ, 1 ≤ W → W ≤ L^(1/125:ℝ) →
      0 ≤ M → W ≤ Real.exp (M/3) →
      Real.sqrt W*(1+Real.log W)*
        (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹) ≤
      101*Real.exp (-M/20)+101*L^(-1/700:ℝ)+majorArcWorkingError W := by
  filter_upwards [major_arc_sharp_energy_rate] with L henergy
  intro W M hW hWL hM hWM
  have hm := major_arc_sharp_distance_rate hW hM hWM
  have he := henergy W hW hWL
  have hi := major_arc_inverse_working_rate hW
  calc
    _ = Real.sqrt W*(1+Real.log W)*Real.exp (-2*M/5)+
        Real.sqrt W*(1+Real.log W)*Real.sqrt (Real.log L/L^(1/80:ℝ))+
        Real.sqrt W*(1+Real.log W)*W⁻¹ := by ring
    _ ≤ _ := add_le_add (add_le_add hm he) hi

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcCorrectedRate
namespace OAI

/-! The correction and character factors fit the exact error exponents
of corrected MRT Theorem 1.7 at the common parameter. -/
namespace TwoPointCorrelations

open _root_.Filter

lemma major_arc_inverse_parameter_error {W : ℝ} (hW : 1 ≤ W) :
    W⁻¹ ≤ majorArcWorkingError W ∧ W^(-5/4:ℝ) ≤ majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  have hi : W⁻¹ ≤ majorArcWorkingError W := by
    calc
      _ = W^(-1:ℝ) := (Real.rpow_neg_one W).symm
      _ ≤ W^(-1/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW])
  refine ⟨hi,?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le hW (show (-5/4:ℝ) ≤ -1 by norm_num)).trans
    (by simpa only [Real.rpow_neg_one] using hi)

theorem major_arc_corrected_published_rate (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ H M : ℝ, 1 ≤ Real.log H →
      1 ≤ Real.log (Real.log H) → 0 ≤ M →
      let W := majorArcParameter L H M
      mrtCorrectionBound*(4*(1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*
        (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹)+3/W)+
        5*W^(-5/4:ℝ)) ≤
      (2500*mrtCorrectionBound*(C+1)*(1+4*Real.pi))*
        (Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
  filter_upwards [major_arc_weighted_energy_rate,major_arc_parameter_rate,
    eventually_ge_atTop (1:ℝ)] with L henergy hparameter hL
  intro H M hH hHH hM
  dsimp only
  let W := majorArcParameter L H M
  let E := Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)
  obtain ⟨hW,hWH,hWL,hWM⟩ := major_arc_parameter_bounds hL hH hM
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hk : majorArcWorkingError W ≤ 21*E := by
    have hh := hparameter H M hH hHH hM
    have he := Real.exp_pos (-M/20)
    have hl : 0 ≤ L^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    have hshort : 0 ≤ Real.log (Real.log H)/Real.log H := by positivity
    rw [mul_div_assoc] at hh
    dsimp only [E,W]
    linarith
  have he : Real.sqrt W*(1+Real.log W)*
      (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹) ≤ 122*E := by
    have hh := henergy W M hW hWL hM hWM
    have hexp := Real.exp_pos (-M/20)
    have hl : 0 ≤ L^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    have hshort : 0 ≤ Real.log (Real.log H)/Real.log H := by positivity
    dsimp only [E] at *
    linarith
  obtain ⟨hinv,hpow⟩ := major_arc_inverse_parameter_error hW
  have hi : 1/W ≤ 21*E := by simpa only [one_div] using hinv.trans hk
  have hp : W^(-5/4:ℝ) ≤ 21*E := hpow.trans hk
  have hb : 0 < mrtCorrectionBound := Real.exp_pos _
  have ht : 0 < 1+4*Real.pi := by positivity
  calc
    _ ≤ mrtCorrectionBound*(4*(1+4*Real.pi)*(4*C*(122*E)+3*(21*E))+5*(21*E)) := by
      apply mul_le_mul_of_nonneg_left _ hb.le
      have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*C by positivity)
      have hm' : 4*C*(Real.sqrt W*(1+Real.log W))*
          (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹) ≤ 4*C*(122*E) := by
        simpa only [mul_assoc] using hm
      have hmain := mul_le_mul_of_nonneg_left
        (add_le_add hm' (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3)))
        (show 0 ≤ 4*(1+4*Real.pi) by positivity)
      have htail := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤5)
      have hs := add_le_add hmain htail
      convert (preTransparency := .instances) hs using 1
      ring
    _ ≤ _ := by
      have hc : (4*(1+4*Real.pi)*(4*C*122+3*21)+5*21) ≤
          2500*(C+1)*(1+4*Real.pi) := by nlinarith [Real.pi_pos]
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hE) hb.le
      convert (preTransparency := .instances) hm using 1 <;> ring

lemma major_arc_rate_volume {A C B x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : C*A ≤ B) : C*x*y*A ≤ B*x*y := by
  calc
    _ = (C*A)*x*y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hx) hy

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNestedQuotients
namespace OAI

/-! The actual nested correction, prefix and gcd quotients. No
identification of a rounded quotient with a real quotient is used. -/

namespace TwoPointCorrelations

lemma mrt_div_add_one_lower (n d : ℕ) (hd : 0 < d) :
    (n:ℝ)/d ≤ (n/d+1:ℕ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  apply le_of_lt
  apply (div_lt_iff₀ hdr).mpr
  have hh : (n:ℝ) < (d:ℝ)*(n/d+1:ℕ) := by
    exact_mod_cast Nat.lt_mul_div_succ n hd
  simpa only [mul_comm] using hh


lemma mrt_nested_prefix_lower {W H : ℝ} {h k d b : ℕ}
    (hW : 0 < W) (hd : 0 < d) (hb : 0 < b)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    H/(W^4*(d:ℝ)*(b:ℝ)) ≤ (k/b+1:ℕ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  have hfirst : (H/W^2)/(d:ℝ) ≤ (h/d+1:ℕ) :=
    (div_le_div_of_nonneg_right hh hdr.le).trans (mrt_div_add_one_lower h d hd)
  have hsecond : ((H/W^2)/(d:ℝ))/W^2 ≤ (k:ℝ) :=
    (div_le_div_of_nonneg_right hfirst (pow_nonneg hW.le _)).trans hk
  have hthird := (div_le_div_of_nonneg_right hsecond hbr.le).trans
    (mrt_div_add_one_lower k b hb)
  calc
    H/(W^4*(d:ℝ)*(b:ℝ)) = (((H/W^2)/(d:ℝ))/W^2)/(b:ℝ) := by
      simp only [div_div]
      congr 1
      ring
    _ ≤ _ := hthird

lemma mrt_nested_prefix_power_lower {W H : ℝ} {h k d b : ℕ}
    (hW : 0 < W) (hH : 0 ≤ H) (hd : 0 < d) (hb : 0 < b)
    (hdW : (d:ℝ) ≤ W^5) (hbW : (b:ℝ) ≤ W)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    H/W^10 ≤ (k/b+1:ℕ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hbr : (0:ℝ) < b := by exact_mod_cast hb
  have hdb := mrt_arc_combined_divisor hW.le hdW hbW
  have hden : W^4*(d:ℝ)*(b:ℝ) ≤ W^10 := by
    calc
      _ = W^4*((d*b:ℕ):ℝ) := by push_cast; ring
      _ ≤ W^4*W^6 := mul_le_mul_of_nonneg_left hdb (pow_nonneg hW.le _)
      _ = _ := by ring
  exact (div_le_div_of_nonneg_left hH (by positivity) hden).trans
    (mrt_nested_prefix_lower hW hd hb hh hk)

lemma mrt_nested_prefix_large {W H : ℝ} {h k d b : ℕ}
    (hW : 1 ≤ W) (hH : W^250 ≤ H) (hd : 0 < d) (hb : 0 < b)
    (hdW : (d:ℝ) ≤ W^5) (hbW : (b:ℝ) ≤ W)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    W^240 ≤ (k/b+1:ℕ) := by
  have hW0 : 0 < W := by linarith
  have hH0 : 0 ≤ H := (pow_nonneg hW0.le 250).trans hH
  calc
    W^240 = W^250/W^10 := by
      rw [show (250:ℕ)=240+10 by decide,pow_add]
      exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hW0.ne')).symm
    _ ≤ H/W^10 := div_le_div_of_nonneg_right hH (pow_nonneg hW0.le _)
    _ ≤ _ := mrt_nested_prefix_power_lower hW0 hH0 hd hb hdW hbW hh hk

lemma mrt_nested_prefix_prime_ratio {W H Q : ℝ} {h k d b : ℕ}
    (hW : 0 < W) (hH : 0 ≤ H) (hQ : Q ≤ H/W^3)
    (hd : 0 < d) (hb : 0 < b) (hdW : (d:ℝ) ≤ W^5) (hbW : (b:ℝ) ≤ W)
    (hh : H/W^2 ≤ (h:ℝ)) (hk : ((h/d+1:ℕ):ℝ)/W^2 ≤ (k:ℝ)) :
    Q/(k/b+1:ℕ) ≤ W^7 := by
  have hlen := mrt_nested_prefix_power_lower hW hH hd hb hdW hbW hh hk
  have hlen0 : (0:ℝ) < (k/b+1:ℕ) := by positivity
  apply (div_le_iff₀ hlen0).mpr
  calc
    Q ≤ H/W^3 := hQ
    _ = W^7*(H/W^10) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlen (pow_nonneg hW.le _)

lemma mrt_nested_prefix_upper {H h k d b : ℕ}
    (hh : h ≤ H) (hk : k ≤ h/d+1) : k/b+1 ≤ H+2 := by
  have hb := Nat.div_le_self k b
  have hd := Nat.div_le_self h d
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTShortSubdivisionSharp
namespace OAI

/-! Subdivision with the exact common outer cutoff.  The last complete
block starts no later than H-h, so its short window stays below X+H. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mrt_subdivision_shift_le {H h j : ℕ} (hj : j ∈ range (H/h)) :
    j*h ≤ H-h := by
  have hs : (j+1)*h ≤ H :=
    (Nat.mul_le_mul_right h (Nat.succ_le_of_lt (mem_range.mp hj))).trans
      (Nat.div_mul_le_self H h)
  rw [Nat.add_mul,one_mul] at hs
  omega

theorem mrt_short_integral_subdivision_sharp (F : ℕ → ℂ) (hF : OneBounded F)
    (X H h : ℕ) (hh : 0 < h) (hhH : h ≤ H) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α+(X:ℝ)*h := by
  have hshift (j : ℕ) (hj : j ∈ range (H/h)) :
      (∑ v ∈ range X, ‖shortExponentialSum F h α (v+j*h:ℕ)‖) ≤
        ∑ v ∈ range (X+H-h), ‖shortExponentialSum F h α v‖ := by
    have hle := mrt_subdivision_shift_le hj
    have hinj : Set.InjOn (fun v : ℕ => v+j*h) (range X) := by
      intro v _ w _ hvw
      exact Nat.add_right_cancel hvw
    calc
      _ = ∑ v ∈ (range X).image (fun v => v+j*h), ‖shortExponentialSum F h α v‖ := by
        rw [sum_image hinj]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro v hv
          obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
          exact mem_range.mpr (by have hw' := mem_range.mp hw; omega)
        · intro v _ _
          exact norm_nonneg _
  simp only [shortExponentialIntegral_eq_sum]
  calc
    _ ≤ ∑ v ∈ range X,
        ((∑ j ∈ range (H/h), ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(h:ℝ)) :=
      sum_le_sum (fun v _ => mrt_short_subdivision_pointwise F hF H h v hh α)
    _ = (∑ j ∈ range (H/h), ∑ v ∈ range X,
        ‖shortExponentialSum F h α (v+j*h:ℕ)‖)+(X:ℝ)*h := by
      rw [sum_add_distrib,sum_comm]
      simp
    _ ≤ (∑ _j ∈ range (H/h), ∑ v ∈ range (X+H-h),
        ‖shortExponentialSum F h α v‖)+(X:ℝ)*h :=
      add_le_add (sum_le_sum hshift) le_rfl
    _ = _ := by simp

theorem mrt_arc_subdivision_integral_sharp (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (hHX : H ≤ X) {W ε : ℝ}
    (hW : 2 ≤ W) (hH : W^(250:ℕ) ≤ (H:ℝ)) (hε : 0 ≤ ε) (α : ℝ)
    (hshort : shortExponentialIntegral F (X+H-mrtArcSubdivisionLength H W)
      (mrtArcSubdivisionLength H W) α ≤
      ε*(X+H-mrtArcSubdivisionLength H W:ℕ)*(mrtArcSubdivisionLength H W:ℝ)) :
    shortExponentialIntegral F X H α ≤
      (X:ℝ)*H*(2*ε+W^(-(1/4:ℝ))) := by
  let h := mrtArcSubdivisionLength H W
  have hh : 0 < h := (mrt_arc_subdivision_bounds hW hH).1
  have hhH : h ≤ H := (mrt_arc_subdivision_bounds hW hH).2.1
  have hH0 : (0:ℝ)< H := (pow_pos (by linarith : 0< W) 250).trans_le hH
  have hcount : (H/h:ℕ)*(h:ℝ) ≤ H := by
    exact_mod_cast Nat.div_mul_le_self H h
  have hX : (X+H-h:ℕ) ≤ (2:ℝ)*X := by
    exact_mod_cast (by omega : X+H-h ≤ 2*X)
  have hmain : (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α ≤
      2*ε*X*H := by
    calc
      _ ≤ (H/h:ℕ)*(ε*(X+H-h:ℕ)*(h:ℝ)) :=
        mul_le_mul_of_nonneg_left hshort (Nat.cast_nonneg _)
      _ = (ε*(X+H-h:ℕ))*((H/h:ℕ)*(h:ℝ)) := by ring
      _ ≤ (ε*((2:ℝ)*X))*(H:ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX hε) hcount
          (by positivity) (by positivity)
      _ = _ := by ring
  have hrem : (X:ℝ)*h ≤ (X:ℝ)*H*W^(-(1/4:ℝ)) := by
    have hb := (div_le_iff₀ hH0).mp (mrt_arc_subdivision_remainder hW hH)
    simpa only [mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg X)
  calc
    _ ≤ (H/h:ℕ)*shortExponentialIntegral F (X+H-h) h α+(X:ℝ)*h :=
      mrt_short_integral_subdivision_sharp F hF X H h hh hhH α
    _ ≤ 2*ε*X*H+(X:ℝ)*H*W^(-(1/4:ℝ)) := add_le_add hmain hrem
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingLength
namespace OAI

/-! Cap the original short length before choosing its prime bands. The
uncapped branch is kept exactly; on the capped branch the omitted final
block is negligible compared with W^(-1/4). -/

namespace TwoPointCorrelations

open _root_.Filter



lemma mrt_working_cap_upper (W : ℝ) :
    (mrtWorkingCap W : ℝ) ≤ Real.exp (Real.sqrt W / 2) :=
  Nat.floor_le (Real.exp_pos _).le

/-- The fixed cap eventually exceeds every prescribed power of W. -/
theorem mrt_working_cap_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, W ^ a ≤ (mrtWorkingCap W : ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hlarge := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually
    (eventually_ge_atTop (8 * ((a : ℝ) + 1)))
  filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  have ht0 : 0 ≤ W ^ (1 / 4 : ℝ) := Real.rpow_nonneg hW0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_nonneg ht0, one_mul] at hs
  have ht2 : (W ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.sqrt_eq_rpow]
    norm_num
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have ham := mul_le_mul_of_nonneg_left hs ha
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hmul := mul_nonneg ht0 (sub_nonneg.mpr ht)
  have he : Real.log 2 + (a : ℝ) * Real.log W ≤ Real.sqrt W / 2 := by
    nlinarith
  have hpow : 2 * W ^ a ≤ Real.exp (Real.sqrt W / 2) := by
    calc
      _ = Real.exp (Real.log 2 + (a : ℝ) * Real.log W) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_nat_mul, Real.exp_log hW0]
      _ ≤ _ := Real.exp_le_exp.mpr he
  have hp : 1 ≤ W ^ a := one_le_pow₀ hW
  have hf := Nat.lt_floor_add_one (Real.exp (Real.sqrt W / 2))
  change Real.exp (Real.sqrt W / 2) < (mrtWorkingCap W : ℝ) + 1 at hf
  linarith

lemma mrt_working_length_upper {H : ℕ} {W : ℝ} :
    mrtWorkingLength H W ≤ H := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact le_rfl
  · have hh : (mrtWorkingCap W : ℝ) ≤ H :=
      (mrt_working_cap_upper W).trans
        ((Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W])).trans (le_of_not_ge h))
    exact_mod_cast hh

lemma mrt_working_length_exp_upper (H : ℕ) (W : ℝ) :
    (mrtWorkingLength H W : ℝ) ≤ Real.exp (Real.sqrt W) := by
  unfold mrtWorkingLength
  split_ifs with h
  · exact h
  · exact (mrt_working_cap_upper W).trans
      (Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg W]))






/-- The bound W ≤ log(H)^5 forces H above any fixed power of W. -/
theorem mrt_working_original_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℝ, 0 < H → 1 ≤ Real.log H →
      W ≤ (Real.log H) ^ (5 : ℕ) → W ^ a ≤ H := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have ht := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop (a : ℝ))
  filter_upwards [hs, ht, eventually_ge_atTop (1 : ℝ)] with W hs ht hW
  have hW0 : 0 < W := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hW), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hW0.le _), one_mul] at hs
  intro H hH0 hlog hWH
  have hp : W ^ (1 / 5 : ℝ) ≤ Real.log H := by
    calc
      _ ≤ ((Real.log H) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow hW0.le hWH (by norm_num)
      _ = Real.log H := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ Real.log H)]
        norm_num
  have ha : (a : ℝ) * Real.log W ≤ W ^ (1 / 5 : ℝ) := by
    calc
      _ ≤ W ^ (1 / 10 : ℝ) * W ^ (1 / 10 : ℝ) :=
        mul_le_mul ht hs (Real.log_nonneg hW) (Real.rpow_nonneg hW0.le _)
      _ = _ := by rw [← Real.rpow_add hW0]; norm_num
  calc
    W ^ a = Real.exp ((a : ℝ) * Real.log W) := by
      rw [Real.exp_nat_mul, Real.exp_log hW0]
    _ ≤ Real.exp (Real.log H) := Real.exp_le_exp.mpr (ha.trans hp)
    _ = H := Real.exp_log hH0

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingLength
namespace OAI

/-! A fifth-root logarithmic cap, obtained from the general square-root
cap by substitution. Its size suits the common Diophantine parameter. -/
namespace TwoPointCorrelations

open _root_.Filter


lemma major_arc_working_root {W : ℝ} (hW : 0 ≤ W) :
    Real.sqrt (W^(2/5:ℝ))=W^(1/5:ℝ) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hW]
  norm_num

lemma major_arc_working_length_le (H : ℕ) (W : ℝ) :
    majorArcWorkingLength H W ≤ H := mrt_working_length_upper


lemma major_arc_working_length_exp_upper (H : ℕ) {W : ℝ} (hW : 0 ≤ W) :
    (majorArcWorkingLength H W:ℝ) ≤ Real.exp (W^(1/5:ℝ)) := by
  simpa only [majorArcWorkingLength,major_arc_working_root hW] using
    mrt_working_length_exp_upper H (W^(2/5:ℝ))

theorem major_arc_working_length_power (a : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) →
      W ≤ Real.log (H:ℝ)^5 → W^a ≤ (majorArcWorkingLength H W:ℝ) := by
  have ht : Tendsto (fun W:ℝ => W^(2/5:ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  filter_upwards [ht.eventually (mrt_working_cap_power (5*a)),
    mrt_working_original_power a,eventually_ge_atTop (1:ℝ)] with W hcap horiginal hW
  intro H hH hlog hWH
  have hW0 : 0 < W := by linarith
  have hc : W^a ≤ (mrtWorkingCap (W^(2/5:ℝ)):ℝ) := by
    apply le_trans _ hcap
    rw [← Real.rpow_mul_natCast hW0.le (2/5:ℝ) (5*a)]
    rw [show (2/5:ℝ)*(5*a:ℕ)=(2:ℝ)*a by push_cast; ring]
    rw [Real.rpow_mul_natCast hW0.le,Real.rpow_two]
    exact pow_le_pow_left₀ hW0.le (by nlinarith) a
  unfold majorArcWorkingLength mrtWorkingLength
  split_ifs
  · exact horiginal H (by exact_mod_cast hH) hlog hWH
  · exact hc



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWorkingOuterScale
namespace OAI

/-! The capped working length fits below the common square-root origin
cutoff. Its boundary remains negligible after the correction division. -/

namespace TwoPointCorrelations

open _root_.Filter

theorem mrt_working_length_add_two_below_sqrt :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ H : ℕ, majorArcWorkingLength H W+2 ≤ ⌈Real.sqrt (X:ℝ)⌉₊ := by
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (show (0:ℝ)<624/625 by norm_num)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hlog.eventually hp,hlog.eventually (eventually_ge_atTop (4:ℝ)),
    eventually_ge_atTop (2:ℕ)] with X hp hL hX
  change 4 ≤ (Real.log (X:ℝ))^(624/625:ℝ) at hp
  intro W hW hWX H
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hpow : (Real.log (X:ℝ))^(1/625:ℝ) ≤ Real.log (X:ℝ)/4 := by
    have he : (Real.log (X:ℝ))^(1/625:ℝ)*
        (Real.log (X:ℝ))^(624/625:ℝ)=Real.log (X:ℝ) := by
      rw [← Real.rpow_add hL0]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg hL0.le (1/625))
    rw [he] at hh
    linarith
  have hroot : W^(1/5:ℝ) ≤ Real.log (X:ℝ)/4 := by
    calc
      _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^(1/5:ℝ) :=
        Real.rpow_le_rpow (by linarith) hWX (by norm_num)
      _ = (Real.log (X:ℝ))^(1/625:ℝ) := by
        rw [← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ _ := hpow
  have hsize : (majorArcWorkingLength H W:ℝ) ≤ Real.exp (Real.log (X:ℝ)/4) :=
    (major_arc_working_length_exp_upper H (by linarith)).trans (Real.exp_le_exp.mpr hroot)
  have he : (Real.exp (Real.log (X:ℝ)/4))^2=Real.sqrt (X:ℝ) := by
    rw [pow_two,← Real.exp_add,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hX0]
    congr 1
    ring
  have htwo : 2 ≤ Real.exp (Real.log (X:ℝ)/4) := by
    linarith [Real.add_one_le_exp (Real.log (X:ℝ)/4)]
  have hsum : (majorArcWorkingLength H W:ℝ)+2 ≤ Real.sqrt (X:ℝ) := by
    nlinarith
  have hh := hsum.trans (Nat.le_ceil (Real.sqrt (X:ℝ)))
  exact_mod_cast hh


theorem mrt_working_quotient_boundary :
    ∀ᶠ X : ℕ in atTop, ∀ W : ℝ, 1 ≤ W →
      W ≤ (Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ d : ℕ, 0 < d → (d:ℝ) ≤ W^5 →
      ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ)/(X/d+1:ℕ) ≤ (W^4)⁻¹ := by
  have hb := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound
    (show (0:ℝ)<1/5 by norm_num)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hb,
    hlog.eventually (eventually_ge_atTop (1:ℝ)),eventually_ge_atTop (2:ℕ)]
    with X hb hL hX
  intro W hW hWX d hd hdW
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0< X by omega)
  have hL0 : 0 < Real.log (X:ℝ) := by linarith
  have hW0 : 0 < W := by linarith
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤ X by omega))),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hX0.le _)] at hb
  have hfive : 5*Real.log (X:ℝ) ≤ Real.sqrt (X:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    linarith
  have hs1 : 1 ≤ Real.sqrt (X:ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast (show 1≤ X by omega))
  have hceil : (⌈Real.sqrt (X:ℝ)⌉₊:ℝ) ≤ 2*Real.sqrt (X:ℝ) := by
    have hh := Nat.ceil_lt_add_one (Real.sqrt_nonneg (X:ℝ))
    linarith
  have hnum : ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ) ≤ 5*Real.sqrt (X:ℝ) := by
    push_cast
    linarith
  have hW9 : W^9 ≤ Real.log (X:ℝ) := by
    calc
      _ ≤ ((Real.log (X:ℝ))^(1/125:ℝ))^9 :=
        pow_le_pow_left₀ hW0.le hWX 9
      _ = (Real.log (X:ℝ))^(9/125:ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
        norm_num
      _ ≤ _ := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          hL (show (9/125:ℝ)≤1 by norm_num)
  have hd4 : (d:ℝ)*W^4 ≤ Real.log (X:ℝ) := by
    calc
      _ ≤ W^5*W^4 := mul_le_mul_of_nonneg_right hdW (pow_nonneg hW0.le _)
      _ = W^9 := by ring
      _ ≤ _ := hW9
  have hprod : ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ)*W^4*(d:ℝ) ≤ X := by
    calc
      _ ≤ (5*Real.sqrt (X:ℝ))*W^4*(d:ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hnum (pow_nonneg hW0.le _)) hd0.le
      _ = (5*Real.sqrt (X:ℝ))*((d:ℝ)*W^4) := by ring
      _ ≤ (5*Real.sqrt (X:ℝ))*Real.log (X:ℝ) :=
        mul_le_mul_of_nonneg_left hd4 (by positivity)
      _ ≤ (Real.sqrt (X:ℝ))^2 := by nlinarith [Real.sqrt_nonneg (X:ℝ)]
      _ = _ := Real.sq_sqrt hX0.le
  have hquot : (X:ℝ)/d < (X/d+1:ℕ) := by
    apply (div_lt_iff₀ hd0).mpr
    have hh : (X:ℝ) < (d:ℝ)*(X/d+1:ℕ) := by
      exact_mod_cast Nat.lt_mul_div_succ X hd
    simpa only [mul_comm] using hh
  have hmul : ((2*⌈Real.sqrt (X:ℝ)⌉₊+1:ℕ):ℝ)*W^4 ≤ (X/d+1:ℕ) :=
    ((le_div_iff₀ hd0).mpr hprod).trans hquot.le
  have hden : (0:ℝ) < (X/d+1:ℕ) := by positivity
  calc
    _ ≤ (((X/d+1:ℕ):ℝ)/W^4)/(X/d+1:ℕ) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ (pow_pos hW0 4)).mpr hmul) hden.le
    _ = _ := by field_simp [hden.ne',hW0.ne']

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcCorrectionGeometry
namespace OAI

/-! Numerical conditions for the actual nested correction and character
windows, including the initial-block boundary and both floor errors. -/
namespace TwoPointCorrelations

open _root_.Finset

lemma major_arc_correction_outer {X V K : ℕ} {W : ℝ}
    (hXV : X ≤ V) (hVX : V+1 ≤ 2*X)
    (hboundary : ∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
      (2*(K:ℝ)+1)/(X/d+1:ℕ) ≤ (W^4)⁻¹) :
    ∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
      V/d+1 ≤ 2*X ∧ (2*(K:ℝ)+1)/(V/d+1:ℕ) ≤ (W^4)⁻¹ := by
  intro d hd hdD
  refine ⟨(Nat.add_le_add_right (Nat.div_le_self V d) 1).trans hVX,?_⟩
  apply le_trans _ (hboundary d hd hdD)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.add_le_add_right (Nat.div_le_div_right hXV) 1

lemma major_arc_correction_window_data {H h K V q : ℕ} {W Q : ℝ}
    (hW : 2 ≤ W) (hH : W^252 ≤ (H:ℝ))
    (hh : (H:ℝ)/W^2 ≤ h) (hhH : h ≤ H) (hhV : h ≤ V)
    (hHK : H+2 ≤ K) (hQ : Q ≤ (H:ℝ)/W^3) (hq : 0 < q) (hqW : (q:ℝ) ≤ W) :
    W^250 ≤ (h:ℝ) ∧
    ∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
      q ≤ V/d+1 ∧ ∀ k : ℕ, 1 ≤ k → k ≤ h/d+1 →
        ((h/d+1:ℕ):ℝ)/W^2 ≤ k → ∀ b ∈ q.divisors,
          4 ≤ k/b+1 ∧ k/b+1 ≤ K ∧ W ≤ (k/b+1:ℕ) ∧ Q/(k/b+1:ℕ) ≤ W^7 := by
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  have hH0 : 0 ≤ (H:ℝ) := Nat.cast_nonneg H
  have hbase : W^250 ≤ (H:ℝ) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (250:ℕ)≤252)).trans hH
  have hlarge : W^250 ≤ (h:ℝ) := by
    apply le_trans _ hh
    apply (le_div_iff₀ (pow_pos hW0 2)).mpr
    simpa only [←pow_add] using hH
  refine ⟨hlarge,?_⟩
  intro d hd hdD
  have hdW : (d:ℝ) ≤ W^5 :=
    (show (d:ℝ) ≤ mrtCorrectionCutoff W by exact_mod_cast hdD).trans
      (mrt_correction_cutoff_bounds hW).2.2
  have hqV : q ≤ V/d+1 := by
    have hlen := mrt_correction_quotient_power hW1 hbase hd hdW hh
    have hsmall : (q:ℝ) ≤ W^243 := hqW.trans (le_self_pow₀ hW1 (by decide))
    have hqhd : q ≤ h/d+1 := by exact_mod_cast hsmall.trans hlen
    exact hqhd.trans (Nat.add_le_add_right (Nat.div_le_div_right hhV) 1)
  refine ⟨hqV,?_⟩
  intro k _ hkh hkl b hb
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hq
  have hbW : (b:ℝ) ≤ W :=
    (show (b:ℝ) ≤ q by exact_mod_cast Nat.le_of_dvd hq (Nat.mem_divisors.mp hb).1).trans hqW
  have hlen := mrt_nested_prefix_large hW1 hbase hd hb0 hdW hbW hh hkl
  have hWlen : W ≤ (k/b+1:ℕ) := (le_self_pow₀ hW1 (by decide : (240:ℕ)≠0)).trans hlen
  have hfour : 4 ≤ (k/b+1:ℕ) := by
    have hfourpow : (4:ℝ) ≤ W^240 := by
      have hs : (4:ℝ) ≤ W^2 := by nlinarith
      exact hs.trans (pow_le_pow_right₀ hW1 (by norm_num : (2:ℕ)≤240))
    exact_mod_cast hfourpow.trans hlen
  exact ⟨hfour,(mrt_nested_prefix_upper hhH hkh).trans hHK,hWlen,
    mrt_nested_prefix_prime_ratio hW0 hH0 hQ hd hb0 hdW hbW hh hkl⟩

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcApproximation
namespace OAI

/-! A reduced rational approximation for the major/minor arc split. -/

namespace TwoPointCorrelations

lemma minor_arc_rational_approximation (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (r : ℤ) (q : ℕ), 0 < q ∧ q ≤ Q ∧ IsCoprime (q : ℤ) r ∧
      |α - (r : ℝ) / q| ≤ 1 / (((Q : ℝ) + 1) * q) ∧
      |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨a, ha, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hQ
  have hq0 : (0 : ℝ) < a.den := by exact_mod_cast a.pos
  have happrox : |α - (a.num : ℝ) / a.den| ≤ 1 / (((Q : ℝ) + 1) * a.den) := by
    simpa only [Rat.cast_def] using ha
  refine ⟨a.num, a.den, a.pos, hden, ?_, happrox, ?_⟩
  · apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using a.reduced.symm
  · apply happrox.trans
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq0)
    have hden' : (a.den : ℝ) ≤ Q := by exact_mod_cast hden
    nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MinorArcAlternative
namespace OAI

/-! The rational approximation used for the major/minor arc alternative,
with its actual short-window denominator cutoff. -/

namespace TwoPointCorrelations

lemma minor_arc_short_rational_approximation (α : ℝ) (H : ℕ) (W : ℝ)
    (hW : 0 < W) (hWH : W ≤ H) :
    ∃ (r : ℤ) (q : ℕ), 0 < q ∧ (q : ℝ) ≤ (H : ℝ) / W ∧
      IsCoprime (q : ℤ) r ∧
      |α - (r : ℝ) / q| ≤ W / ((H : ℝ) * q) ∧
      |α - (r : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  let Q : ℕ := ⌊(H : ℝ) / W⌋₊
  have hQ : 0 < Q := Nat.floor_pos.mpr ((le_div_iff₀ hW).mpr (by simpa using hWH))
  obtain ⟨r, q, hq, hqQ, hcop, happ, hsquare⟩ := minor_arc_rational_approximation α Q hQ
  have hcut : (q : ℝ) ≤ (H : ℝ) / W :=
    (by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans (Nat.floor_le (by positivity))
  have hH : (0 : ℝ) < H := hW.trans_le hWH
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hQlarge : (H : ℝ) ≤ ((Q : ℝ) + 1) * W :=
    (div_le_iff₀ hW).mp (Nat.lt_floor_add_one ((H : ℝ) / W)).le
  refine ⟨r, q, hq, hcut, hcop, happ.trans ?_, hsquare⟩
  apply (div_le_div_iff₀ (mul_pos hQ0 hq0) (mul_pos hH hq0)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hQlarge hq0.le]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.MajorArcWorkingMean
namespace OAI

/-! The major arcs at the actual common parameter and working length.
The only band hypothesis is the geometry of the common final index,
which is supplied independently by `mrt_working_parameters`. -/
namespace TwoPointCorrelations

open _root_.Finset _root_.Filter

theorem major_arc_actual_working_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X → ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
    ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      MRTDistanceLowerBound F X H M → ∀ r : ℤ, ∀ q : ℕ,
      0 < q → (q:ℝ) ≤ W → ∀ β : ℝ, |β| ≤ W/((h:ℝ)*q) →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h ((r:ℝ)/q+β) ≤
      C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C,hC,N₀,hcorrect⟩ := major_arc_corrected_typical_mean hprime hhigh
  obtain ⟨W₁,X₁,hparams⟩ := mrt_working_parameters
  obtain ⟨W₂,hpower⟩ := eventually_atTop.mp (major_arc_working_length_power 252)
  let D := 2500*mrtCorrectionBound*(C+1)*(1+4*Real.pi)
  have hCB : 0 < mrtCorrectionBound := Real.exp_pos _
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := (hlog.eventually (major_arc_corrected_published_rate C hC.le)).and
    (hlog.eventually major_arc_parameter_rate)
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (hlarge.and (mrt_working_length_add_two_below_sqrt.and
      (mrt_working_quotient_boundary.and
        ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and
          (eventually_ge_atTop (max X₁ (max 2 (N₀^2))))))))
  refine ⟨2*D+21,by positivity,max 2 (max W₁ W₂),X₂,?_⟩
  intro X H hXX₂ hH hHX hLH hLL M hM
  dsimp only
  intro hW₀ Y hXY hY J hJ hbands F hF1 hFm hFb hd r q hq hqW β hβ
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let K := ⌈Real.sqrt (X:ℝ)⌉₊
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  change Y+h ≤ 2*X at hY
  obtain ⟨hfinal,houter⟩ := hX₂ X hXX₂
  obtain ⟨hcap,hboundary,hLX,hxmin⟩ := houter
  have hX : 2 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hxmin)
  have hXX : X₁ ≤ X := (le_max_left _ _).trans hxmin
  have hN : N₀^2 ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hxmin)
  have hW : 2 ≤ W := (le_max_left _ _).trans hW₀
  have hWW₁ : W₁ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW₀)
  have hWW₂ : W₂ ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hW₀)
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  obtain ⟨_,hWH,hWX,_⟩ := major_arc_parameter_bounds hLX hLH hM
  have hpow : W^252 ≤ (h:ℝ) := hpower W hWW₂ H (by omega) hLH hWH
  have hpow250 : W^250 ≤ (h:ℝ) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (250:ℕ)≤252)).trans hpow
  have hh : 0 < h := by
    have hp : (0:ℝ) < h := (pow_pos hW0 252).trans_le hpow
    exact_mod_cast hp
  have hhX : h ≤ X := (major_arc_working_length_le H W).trans hHX
  have hcapK : h+2 ≤ K := hcap W hW1 hWX H
  have hKX : K ≤ X := by
    apply Nat.ceil_le.mpr
    exact Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast (show 1≤ X by omega)))
  have hK : 1 ≤ K := by omega
  have hNK : N₀ ≤ K := by
    have hn : (N₀:ℝ)^2 ≤ X := by exact_mod_cast hN
    have hs : (N₀:ℝ) ≤ Real.sqrt (X:ℝ) := by
      nlinarith only [hn,Real.sq_sqrt (Nat.cast_nonneg X),Real.sqrt_nonneg (X:ℝ),(show (0:ℝ)≤ N₀ from Nat.cast_nonneg N₀)]
    exact_mod_cast hs.trans (Nat.le_ceil (Real.sqrt (X:ℝ)))
  obtain ⟨hprimepars,_,_⟩ := hparams W hWW₁ H (by omega) hLH hWH X hXX hWX
  obtain ⟨hP,hPQ,hLP,hLQ,hbudget,hres100,hres⟩ := hprimepars
  have hQK : 2*Q ≤ K := by
    have hp := (hparams W hWW₁ H (by omega) hLH hWH X hXX hWX).2.1.2
    exact hp
  have hWK : W ≤ K :=
    ((le_self_pow₀ hW1 (by decide : (252:ℕ)≠0)).trans hpow).trans
      (by exact_mod_cast (show h≤ K by omega))
  have hWR : W^9 ≤ mrtBaseResolution P Q (1/100) :=
    (pow_le_pow_right₀ hW1 (by norm_num : (9:ℕ)≤100)).trans hres100
  have hWP : W^5 ≤ P := pow_le_pow_right₀ hW1 (by norm_num : (5:ℕ)≤500000)
  let s := mrtArcSubdivisionLength h W
  obtain ⟨hs, hsh, hslo, _⟩ := mrt_arc_subdivision_bounds hW hpow250
  let V := Y+h-s
  have hVH : s ≤ V := by dsimp [V]; omega
  have hwin := major_arc_correction_window_data hW hpow hslo hsh hVH hcapK
    (le_refl Q) hq hqW
  have houter' := major_arc_correction_outer (show X≤ V by dsimp [V]; omega)
    (show V+1≤2*X by dsimp [V]; omega)
    (fun d hdp hdD => by
      have hdpow : (d:ℝ) ≤ W^5 :=
        (show (d:ℝ) ≤ mrtCorrectionCutoff W by exact_mod_cast hdD).trans
          (mrt_correction_cutoff_bounds hW).2.2
      simpa only [K,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
        hboundary W hW1 hWX d hdp hdpow)
  have hqmax : (q:ℝ) ≤ mrtModulusCutoff X H :=
    hqW.trans (le_min hWX hWH)
  have hqinv : 1/(q:ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1)
      (show (1:ℝ)≤ q by exact_mod_cast hq)
  have hphase : |β| *(s:ℝ) ≤ 1 :=
    (mrt_arc_subdivision_phase hW hpow250 hq hβ).trans hqinv
  have hm := hcorrect X V s K H hX hLX hVH hNK hK (Nat.le_ceil _)
    P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hbands W hW hWK hWR hWP
    hwin.1 houter' q hq hqW hqmax hwin.2 F hF1 hFm hFb M hM hd r β hphase
  let E := Real.exp (-M/20)+mrtShortError X H
  have hE : 0 ≤ E := by
    unfold E mrtShortError
    positivity
  have hrate := hfinal.1 H M hLH hLL hM
  have hm' : shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
      V s ((r:ℝ)/q+β) ≤ (D*E)*(V:ℝ)*s := by
    apply hm.trans
    have hrate' : mrtCorrectionBound*(4*(1+4*Real.pi)*
        (4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W)+
          5*W^(-5/4:ℝ)) ≤ D*E := by
      simpa only [W,D,E,mrtShortError,add_assoc] using hrate
    exact major_arc_rate_volume (Nat.cast_nonneg V) (Nat.cast_nonneg s) hrate'
  have hsfull := mrt_arc_subdivision_integral_sharp _
    (mrtTypicalCoefficient_oneBounded _ _ F hFb) Y h (hhX.trans hXY) hW hpow250
    (mul_nonneg hD.le hE) ((r:ℝ)/q+β) hm'
  have htail : W^(-1/4:ℝ) ≤ 21*E := by
    have hk := hfinal.2 H M hLH hLL hM
    have hsmall : W^(-1/4:ℝ) ≤ majorArcWorkingError W := by
      apply (Real.rpow_le_rpow_of_exponent_le hW1 (show (-1/4:ℝ)≤-1/5 by norm_num)).trans
      exact le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW1])
    have hshort : 0 ≤ Real.log (Real.log (H:ℝ))/Real.log H := by positivity
    have hlogerr : 0 ≤ (Real.log X)^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    have hexp := Real.exp_pos (-M/20)
    rw [mul_div_assoc] at hk
    dsimp [E,mrtShortError]
    linarith only [hk,hsmall,hshort,hlogerr,hexp]
  calc
    _ ≤ (Y:ℝ)*h*(2*(D*E)+W^(-1/4:ℝ)) := by simpa only [neg_div] using hsfull
    _ ≤ (Y:ℝ)*h*(2*(D*E)+21*E) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity)
    _ = _ := by dsimp only [E]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTypicalWorkingMean
namespace OAI

/-! The rational major/minor alternative for the actual working bands.
The same finite family works for every additive frequency and every
allowed origin range. -/
namespace TwoPointCorrelations

open _root_.Filter _root_.Finset

theorem mrt_typical_actual_working_mean_oai
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∃ X₀ : ℕ,
    ∀ X H : ℕ, X₀ ≤ X → 10 ≤ H → H ≤ X →
      1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter (Real.log X) H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∃ J : ℕ, 1 ≤ J ∧
        (∀ j ∈ Icc 1 J, Real.log (mrtBandUpper Q j) ≤ Real.sqrt (Real.log X)/2) ∧
      ∀ Y : ℕ, X ≤ Y → Y+h ≤ 2*X →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
        MRTDistanceLowerBound F X H M → ∀ α : ℝ,
        shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
        C*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C₁,hC₁,W₁,X₁,hmajor⟩ := major_arc_actual_working_mean hprime hhigh
  obtain ⟨C₂,hC₂,W₂,hminor⟩ := minor_arc_actual_working_mean
  obtain ⟨W₃,X₃,hpar⟩ := mrt_working_parameters
  obtain ⟨W₄,hpow⟩ := eventually_atTop.mp (major_arc_working_length_power 1)
  have hlog : Tendsto (fun X:ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₄,hX₄⟩ := eventually_atTop.mp
    ((hlog.eventually hminor).and
      ((hlog.eventually (eventually_ge_atTop (1:ℝ))).and
        (eventually_ge_atTop (max X₁ X₃))))
  refine ⟨C₁+C₂,by positivity,max W₁ (max W₂ (max W₃ W₄)),X₄,?_⟩
  intro X H hX hH hHX hLH hLL M hM
  dsimp only
  intro hWlarge
  let W := majorArcParameter (Real.log X) H M
  let h := majorArcWorkingLength H W
  let P := W^(500000:ℕ)
  let Q := (h:ℝ)/W^3
  obtain ⟨hm,hLX,hXs⟩ := hX₄ X hX
  have hX₁ : X₁ ≤ X := (le_max_left _ _).trans hXs
  have hX₃ : X₃ ≤ X := (le_max_right _ _).trans hXs
  have hW₁ : W₁ ≤ W := (le_max_left _ _).trans hWlarge
  have hW₂ : W₂ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWlarge)
  have hW₃ : W₃ ≤ W := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hWlarge))
  have hW₄ : W₄ ≤ W := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hWlarge))
  obtain ⟨hW,hWH,hWX,_⟩ := major_arc_parameter_bounds hLX hLH hM
  have hW0 : 0 < W := by linarith
  have hWh : W ≤ (h:ℝ) := by
    simpa only [pow_one] using hpow W hW₄ H (by omega) hLH hWH
  obtain ⟨_,_,J,hJ,_,_,hup,hbands⟩ := hpar W hW₃ H (by omega) hLH hWH X hX₃ hWX
  refine ⟨J,hJ,hup,?_⟩
  intro Y hXY hY F hF1 hFm hFb hd α
  have hE : 0 ≤ Real.exp (-M/20)+mrtShortError X H := by
    unfold mrtShortError
    positivity
  obtain ⟨r,q,hq,hqh,hcop,happ,hsq⟩ := minor_arc_short_rational_approximation α h W hW0 hWh
  by_cases hqW : (q:ℝ) ≤ W
  · have hb : ∀ n : ℕ, ⌈Real.sqrt (X:ℝ)⌉₊ ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n)) := by
      intro n hn hnX
      exact hbands n hn (by omega)
    have ha := hmajor X H hX₁ hH hHX hLH hLL M hM hW₁ Y hXY hY J hJ hb
      F hF1 hFm hFb hd r q hq hqW (α-(r:ℝ)/q) happ
    rw [show (r:ℝ)/q+(α-(r:ℝ)/q)=α by ring] at ha
    apply ha.trans
    have hh := mul_le_mul_of_nonneg_right (show C₁ ≤ C₁+C₂ from le_add_of_nonneg_right hC₂.le)
      (show 0≤(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) by positivity)
    convert (preTransparency := .instances) hh using 1 <;> ring
  · have hWY : h ≤ Y := (major_arc_working_length_le H W).trans (hHX.trans hXY)
    have ha := hm H (by omega) hLH hLL M hM hW₂ Y J hWY hJ F hFm hFb
      r q (le_of_not_ge hqW) hqh α hcop hsq
    have ha' : shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
        C₂*(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) := by
      simpa only [mrtShortError,add_assoc] using ha
    apply ha'.trans
    have hh := mul_le_mul_of_nonneg_right (show C₂ ≤ C₁+C₂ from le_add_of_nonneg_left hC₁.le)
      (show 0≤(Y:ℝ)*h*(Real.exp (-M/20)+mrtShortError X H) by positivity)
    convert (preTransparency := .instances) hh using 1 <;> ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_typical_actual_working_mean_oai := @OAI.TwoPointCorrelations.mrt_typical_actual_working_mean_oai
