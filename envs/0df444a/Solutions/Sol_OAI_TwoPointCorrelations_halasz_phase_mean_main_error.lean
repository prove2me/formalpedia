-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_phase_mean_main_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:34:29.711988+00:00
-- url     : https://prove2.me/submissions/7eb058ef-220b-4bce-9b21-b999777d6f6f

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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

/-- Coprime arguments have disjoint prime support, so arbitrary prime-power
values give an ordinary multiplicative function. -/
theorem fromPrimePowers_multiplicative (F : ℕ → ℕ → ℂ) :
    Multiplicative (fromPrimePowers F) := by
  intro m n hm hn hcop
  unfold fromPrimePowers
  rw [Nat.factorization_mul hm.ne' hn.ne']
  apply Finsupp.prod_add_index_of_disjoint
  simpa only [Nat.support_factorization] using hcop.disjoint_primeFactors


@[simp] theorem fromPrimePowers_prime (F : ℕ → ℕ → ℂ) {p : ℕ} (hp : Nat.Prime p) :
    fromPrimePowers F p = F p 1 := by
  simp [fromPrimePowers, hp.factorization, Finsupp.prod]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbola
namespace OAI

/-! The exact finite hyperbola decomposition underlying Halász's
logarithmic mean-value identity. All endpoints are positive integers. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem halasz_sum_divisorsAntidiagonal (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2) =
      ∑ p ∈ halaszHyperbola N, F p.1 p.2 := by
  rw [sum_sigma' (Icc 1 N) (fun n => n.divisorsAntidiagonal) (fun _ p => F p.1 p.2)]
  apply sum_bij (fun x _ => x.2)
  · intro x hx
    obtain ⟨hn, hp⟩ := mem_sigma.mp hx
    obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hpos : 0 < x.2.1 * x.2.2 := by rw [hmul]; exact (mem_Icc.mp hn).1
    have h₁ : 1 ≤ x.2.1 := Nat.pos_of_mul_pos_right hpos
    have h₂ : 1 ≤ x.2.2 := Nat.pos_of_mul_pos_left hpos
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨h₁, ?_⟩, mem_Icc.mpr ⟨h₂, ?_⟩⟩, ?_⟩
    · calc
        _ ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_right _ h₂
        _ = x.1 := hmul
        _ ≤ N := (mem_Icc.mp hn).2
    · calc
        _ ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_left _ h₁
        _ = x.1 := hmul
        _ ≤ N := (mem_Icc.mp hn).2
    · exact hmul ▸ (mem_Icc.mp hn).2
  · intro x hx y hy hxy
    obtain ⟨_, hpx⟩ := mem_sigma.mp hx
    obtain ⟨_, hpy⟩ := mem_sigma.mp hy
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp hpx).1
    have hyprod := (Nat.mem_divisorsAntidiagonal.mp hpy).1
    have hn : x.1 = y.1 := by rw [← hxprod, ← hyprod, hxy]
    cases x
    cases y
    simp_all
  · intro p hp
    obtain ⟨hp, hprod⟩ := mem_filter.mp hp
    obtain ⟨h₁, h₂⟩ := mem_product.mp hp
    have hpos : 0 < p.1 * p.2 := Nat.mul_pos (mem_Icc.mp h₁).1 (mem_Icc.mp h₂).1
    refine ⟨⟨p.1 * p.2, p⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨hpos, hprod⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, Nat.ne_of_gt hpos⟩⟩, rfl⟩
  · intro x _
    rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbolaRows
namespace OAI

/-! Row decomposition of the finite positive hyperbola. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem halasz_hyperbola_rows (F : ℕ → ℕ → ℂ) (N : ℕ) :
    (∑ p ∈ halaszHyperbola N, F p.1 p.2) =
      ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d m := by
  classical
  simp only [halaszHyperbola, sum_filter, Finset.product_eq_sprod]
  rw [sum_product (Icc 1 N) (Icc 1 N)
    (fun p : ℕ × ℕ => if p.1 * p.2 ≤ N then F p.1 p.2 else 0)]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter]
  apply sum_congr ?_ (fun _ _ => rfl)
  ext m
  have hdpos := (mem_Icc.mp hd).1
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hm, _⟩, hprod⟩
    refine ⟨hm, (Nat.le_div_iff_mul_le hdpos).mpr ?_⟩
    simpa only [Nat.mul_comm] using hprod
  · rintro ⟨hm, hquot⟩
    refine ⟨⟨hm, hquot.trans (Nat.div_le_self N d)⟩, ?_⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hquot

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




lemma fromPrimePowers_prime_pow (F : ℕ → ℕ → ℂ)
    (hF : ∀ p, F p 0 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    fromPrimePowers F (p ^ k) = F p k := by
  unfold fromPrimePowers
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (hF p)




@[simp] lemma mrtCorrectionLocal_zero (f : ℕ → ℂ) (p : ℕ) :
    mrtCorrectionLocal f p 0 = 1 := by
  simp [mrtCorrectionLocal]

@[simp] lemma mrtCorrectionLocal_one (f : ℕ → ℂ) (h1 : f 1 = 1) (p : ℕ) :
    mrtCorrectionLocal f p 1 = 0 := by
  simp [mrtCorrectionLocal, h1]






@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := if_neg hn.ne'

lemma mrtArithmetic_isMultiplicative (f : ℕ → ℂ) (hf : Multiplicative f)
    (h1 : f 1 = 1) : (mrtArithmetic f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [h1], ?_⟩
  intro m n hm hn hcop
  simp only [mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hm),
    mrtArithmetic_apply_pos _ (Nat.pos_of_ne_zero hn),
    mrtArithmetic_apply_pos _ (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn))]
  exact hf m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop



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

lemma halaszUnitCorrectionLocal_succ (F : ℕ → ℂ) (p k : ℕ) :
    halaszUnitCorrectionLocal F p (k + 1) = F (p ^ (k + 1)) - F (p ^ k) := by
  simp [halaszUnitCorrectionLocal]

lemma halasz_unit_correction_prime_pow (F : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    halaszUnitCorrection F (p ^ k) = halaszUnitCorrectionLocal F p k :=
  fromPrimePowers_prime_pow _ (halaszUnitCorrectionLocal_zero F) hp k


lemma halasz_unit_correction_local_sum (F : ℕ → ℂ) (hF : F 1 = 1) (p k : ℕ) :
    (∑ i ∈ range (k + 1), halaszUnitCorrectionLocal F p i) = F (p ^ k) := by
  induction k with
  | zero => simp [hF]
  | succ k ih =>
    rw [sum_range_succ, ih, halaszUnitCorrectionLocal_succ]
    ring

lemma halasz_unit_correction_convolution (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) :
    mrtArithmetic (halaszUnitCorrection F) * mrtArithmetic (fun _ => 1) = mrtArithmetic F := by
  have hh : (mrtArithmetic (halaszUnitCorrection F)).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fromPrimePowers_multiplicative _) (fromPrimePowers_one _)
  have hu : (mrtArithmetic (fun _ => (1 : ℂ))).IsMultiplicative :=
    mrtArithmetic_isMultiplicative _ (fun _ _ _ _ _ => (one_mul (1 : ℂ)).symm) rfl
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hh.mul hu)
    _ (mrtArithmetic_isMultiplicative F hF hF1)).mpr
  intro p k hp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (halaszUnitCorrection F) a * mrtArithmetic (fun _ => 1) b),
    Nat.sum_divisors_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), halaszUnitCorrectionLocal F p i := by
      apply sum_congr rfl
      intro i hi
      have hik : i ≤ k := by have := mem_range.mp hi; omega
      rw [mrtArithmetic_apply_pos _ (pow_pos hp.pos i), Nat.pow_div hik hp.pos,
        mrtArithmetic_apply_pos _ (pow_pos hp.pos (k - i)), mul_one,
        halasz_unit_correction_prime_pow F hp]
    _ = _ := by rw [halasz_unit_correction_local_sum F hF1,
      mrtArithmetic_apply_pos _ (pow_pos hp.pos k)]

lemma halasz_unit_correction_divisor_sum (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) {n : ℕ} (hn : 0 < n) :
    F n = ∑ d ∈ n.divisors, halaszUnitCorrection F d := by
  have he := congrArg (fun a : ArithmeticFunction ℂ => a n)
    (halasz_unit_correction_convolution F hF hF1)
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => mrtArithmetic (halaszUnitCorrection F) a * mrtArithmetic (fun _ => 1) b),
    mrtArithmetic_apply_pos _ hn] at he
  rw [← he]
  apply sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisors.mp hd).1
  have hd0 := Nat.pos_of_dvd_of_pos hdn hn
  have hquot : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  rw [mrtArithmetic_apply_pos _ hd0, mrtArithmetic_apply_pos _ hquot, mul_one]



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseTaylor
namespace OAI

/-! Local phase expansion for the elementary near-twist sum comparison.
The linear term cancels on intervals centered at an integer. -/

namespace TwoPointCorrelations

open scoped _root_.ComplexConjugate

lemma halasz_log_one_add_small (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ u ^ 2 ∧ |Real.log (1 + u)| ≤ 3 / 2 * |u| := by
  have hp : 0 ≤ 1 + u := by linarith [(abs_le.mp hu).1]
  have hn : ‖(u : ℂ)‖ ≤ 1 / 2 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hu
  have he : Complex.log (1 + (u : ℂ)) = (Real.log (1 + u) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_log hp]
  have hfirst := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hn (by norm_num))
  have hsecond := Complex.norm_log_one_add_half_le_self hn
  rw [he, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs] at hfirst
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at hsecond
  refine ⟨hfirst.trans ?_, hsecond⟩
  have hi : (1 - |u|)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 1 - |u|)).mpr
    linarith
  rw [sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg u)]

lemma halasz_phase_linear_error (t u : ℝ) (hu : |u| ≤ 1 / 2)
    (htu : |t * u| ≤ 1 / 2) :
    ‖Complex.exp (((-t * Real.log (1 + u) : ℝ) : ℂ) * Complex.I) - 1 -
        (((-t * u : ℝ) : ℂ) * Complex.I)‖ ≤ 4 * (t ^ 2 + |t|) * u ^ 2 := by
  obtain ⟨hlog, hsize⟩ := halasz_log_one_add_small u hu
  let a : ℝ := -t * Real.log (1 + u)
  let b : ℝ := -t * u
  have ha : |a| ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hsize (abs_nonneg t)
    rw [abs_mul] at htu
    dsimp [a]
    rw [abs_mul, abs_neg]
    nlinarith
  have hcn : ‖(a : ℂ) * Complex.I‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] using ha
  have hexp := Complex.norm_exp_sub_one_sub_id_le hcn
  have hab : |a - b| ≤ |t| * u ^ 2 := by
    have he : a - b = -t * (Real.log (1 + u) - u) := by dsimp [a, b]; ring
    rw [he, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg t)
  have ha2 : a ^ 2 ≤ 9 / 4 * t ^ 2 * u ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (Real.log (1 + u))) hsize 2
    rw [sq_abs, mul_pow, sq_abs] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
    dsimp [a]
    nlinarith
  have hsplit : Complex.exp ((a : ℂ) * Complex.I) - 1 - (b : ℂ) * Complex.I =
      (Complex.exp ((a : ℂ) * Complex.I) - 1 - (a : ℂ) * Complex.I) +
        ((a - b : ℝ) : ℂ) * Complex.I := by push_cast; ring
  change ‖Complex.exp ((a : ℂ) * Complex.I) - 1 - (b : ℂ) * Complex.I‖ ≤ _
  rw [hsplit]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    sq_abs] at hexp ⊢
  have hn : 0 ≤ |t| * u ^ 2 := by positivity
  have hn2 : 0 ≤ t ^ 2 * u ^ 2 := by positivity
  nlinarith

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

lemma halasz_power_phase_add (t x y : ℝ) (hx : 0 < x) (hxy : 0 < x + y) :
    halaszPowerPhase t (x + y) = halaszPowerPhase t x *
      Complex.exp (((-t * Real.log (1 + y / x) : ℝ) : ℂ) * Complex.I) := by
  have he : x + y = x * (1 + y / x) := by field_simp
  have hp : 0 < 1 + y / x := by rw [← mul_pos_iff_of_pos_left hx, ← he]; exact hxy
  rw [halaszPowerPhase, he, Real.log_mul hx.ne' hp.ne', mul_add,
    Complex.ofReal_add, add_mul, Complex.exp_add]
  rfl

lemma halasz_power_phase_cell_error (t x y : ℝ) (hx : 1 ≤ x)
    (ht : |t| ≤ x) (hy : |y| ≤ 1 / 2) :
    ‖halaszPowerPhase t (x + y) -
      halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I))‖ ≤
      (t ^ 2 + |t|) / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hxy : 0 < x + y := by linarith [(abs_le.mp hy).1]
  have hratio : |y / x| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hx0]
    apply (div_le_iff₀ hx0).mpr
    linarith
  have htratio : |t * (y / x)| ≤ 1 / 2 := by
    rw [abs_mul, abs_div, abs_of_pos hx0]
    calc
      _ ≤ x * ((1 / 2) / x) := mul_le_mul ht
        (div_le_div_of_nonneg_right hy hx0.le) (by positivity) hx0.le
      _ = 1 / 2 := by field_simp
  have hh := halasz_phase_linear_error t (y / x) hratio htratio
  have he : halaszPowerPhase t (x + y) -
      halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I)) =
      halaszPowerPhase t x *
        (Complex.exp (((-t * Real.log (1 + y / x) : ℝ) : ℂ) * Complex.I) - 1 -
          (((-t * (y / x) : ℝ) : ℂ) * Complex.I)) := by
    rw [halasz_power_phase_add t x y hx0 hxy]
    ring
  rw [he, norm_mul, halasz_power_phase_norm, one_mul]
  apply hh.trans
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg y) hy 2
    norm_num [sq_abs] at hh
    exact hh
  rw [div_pow]
  calc
    _ ≤ 4 * (t ^ 2 + |t|) * ((1 / 4) / x ^ 2) := by gcongr
    _ = _ := by ring


lemma halasz_power_phase_cell_integral (t x : ℝ) (hx : 1 ≤ x) (ht : |t| ≤ x) :
    ‖(∫ y in (-1 / 2 : ℝ)..(1 / 2 : ℝ), halaszPowerPhase t (x + y)) -
      halaszPowerPhase t x‖ ≤ (t ^ 2 + |t|) / x ^ 2 := by
  let lin : ℝ → ℂ := fun y =>
    halaszPowerPhase t x * (1 + (((-t * (y / x) : ℝ) : ℂ) * Complex.I))
  have hlin : Continuous lin := by dsimp [lin]; fun_prop
  have hf : ContinuousOn (fun y => halaszPowerPhase t (x + y))
      (Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
    have hne : ∀ y ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ), x + y ≠ 0 := by
      intro y hy
      rw [Set.uIcc_of_le (by norm_num)] at hy
      have hp : 0 < x + y := by linarith [hy.1]
      exact hp.ne'
    unfold halaszPowerPhase
    fun_prop (disch := assumption)
  have hli : (∫ y in (-1 / 2 : ℝ)..(1 / 2 : ℝ), lin y) = halaszPowerPhase t x := by
    dsimp [lin]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_div, integral_id]
      norm_num
    · exact continuous_const.intervalIntegrable _ _
    · exact (by fun_prop : Continuous (fun y : ℝ =>
        (((-t * (y / x) : ℝ) : ℂ) * Complex.I))).intervalIntegrable _ _
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (f := fun y => halaszPowerPhase t (x + y) - lin y)
    (C := (t ^ 2 + |t|) / x ^ 2) (fun y hy => by
      apply halasz_power_phase_cell_error t x y hx ht
      rw [Set.uIoc_of_le (by norm_num)] at hy
      exact abs_le.mpr ⟨by linarith [hy.1], hy.2⟩)
  rw [intervalIntegral.integral_sub hf.intervalIntegrable (hlin.intervalIntegrable _ _), hli] at hh
  norm_num at hh ⊢
  exact hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseIntegral
namespace OAI

/-! Exact primitive of the Archimedean phase, including the zero endpoint. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory

lemma halasz_power_phase_eq_cpow (t x : ℝ) (hx : 0 < x) :
    halaszPowerPhase t x = (x : ℂ) ^ ((-t : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold halaszPowerPhase
  congr 1
  push_cast
  ring

lemma halasz_power_phase_cpow_primitive (t x : ℝ) (hx : 0 ≤ x) :
    (x : ℂ) ^ ((-t : ℂ) * Complex.I + 1) = (x : ℂ) * halaszPowerPhase t x := by
  by_cases hx0 : x = 0
  · subst x
    simp only [Complex.ofReal_zero, zero_mul]
    apply Complex.zero_cpow
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Complex.cpow_add _ _ (by exact_mod_cast hx0), Complex.cpow_one,
      halasz_power_phase_eq_cpow t x hxp, mul_comm]

lemma halasz_power_phase_integral (t a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in a..b, halaszPowerPhase t x) =
      ((b : ℂ) * halaszPowerPhase t b - (a : ℂ) * halaszPowerPhase t a) /
        (1 + (-t : ℂ) * Complex.I) := by
  have he : (∫ x in a..b, halaszPowerPhase t x) =
      ∫ x : ℝ in a..b, (x : ℂ) ^ ((-t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    exact halasz_power_phase_eq_cpow t x
      (lt_of_le_of_lt (le_min ha hb) hx.1)
  rw [he, integral_cpow (Or.inl (by norm_num [Complex.mul_re])),
    halasz_power_phase_cpow_primitive t b hb,
    halasz_power_phase_cpow_primitive t a ha, add_comm ((-t : ℂ) * Complex.I) 1]

lemma halasz_power_phase_intervalIntegrable (t a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (halaszPowerPhase t) volume a b := by
  apply (intervalIntegral.intervalIntegrable_cpow' (r := (-t : ℂ) * Complex.I)
    (by norm_num [Complex.mul_re])).congr_uIoo
  intro x hx
  exact (halasz_power_phase_eq_cpow t x
    (lt_of_le_of_lt (le_min ha hb) hx.1)).symm

lemma halasz_power_phase_integral_norm (t a b : ℝ) :
    ‖∫ x in a..b, halaszPowerPhase t x‖ ≤ |b - a| := by
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 1) (f := halaszPowerPhase t)
    (fun x _ => (halasz_power_phase_norm t x).le)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseSum
namespace OAI

/-! A uniform power-sum estimate, using centered cells past the frequency. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory _root_.Finset

lemma halasz_phase_cells_telescope (t : ℝ) (A N : ℕ) (hA : 1 ≤ A) (hAN : A ≤ N) :
    (∑ n ∈ Ioc A N, ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2),
      halaszPowerPhase t x) =
      ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ N hAN ih =>
    rw [sum_Ioc_succ_top hAN, ih]
    have he : ((N + 1 : ℕ) : ℝ) - 1 / 2 = (N : ℝ) + 1 / 2 := by push_cast; ring
    rw [he]
    apply intervalIntegral.integral_add_adjacent_intervals
    · exact halasz_power_phase_intervalIntegrable t ((A : ℝ) + 1 / 2)
        ((N : ℝ) + 1 / 2) (by positivity) (by positivity)
    · exact halasz_power_phase_intervalIntegrable t ((N : ℝ) + 1 / 2)
        (((N + 1 : ℕ) : ℝ) + 1 / 2) (by positivity) (by positivity)

lemma halasz_phase_cell_sum_error (t : ℝ) (A N : ℕ) (hA : 1 ≤ A)
    (hAN : A ≤ N) (ht : |t| ≤ (A : ℝ)) :
    ‖(∑ n ∈ Ioc A N, halaszPowerPhase t n) -
      ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤
      (t ^ 2 + |t|) / A := by
  rw [← halasz_phase_cells_telescope t A N hA hAN, ← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc A N,
        ‖halaszPowerPhase t n -
          ∫ x in ((n : ℝ) - 1 / 2)..((n : ℝ) + 1 / 2), halaszPowerPhase t x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Ioc A N, (t ^ 2 + |t|) / (n : ℝ) ^ 2 := by
      apply sum_le_sum
      intro n hn
      have hnA := (mem_Ioc.mp hn).1
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hA.trans hnA.le
      have htn : |t| ≤ (n : ℝ) := ht.trans (by exact_mod_cast hnA.le)
      have hh := halasz_power_phase_cell_integral t n hn1 htn
      rw [intervalIntegral.integral_comp_add_left] at hh
      have he : (n : ℝ) + (-1 / 2) = (n : ℝ) - 1 / 2 := by ring
      rw [he] at hh
      simpa only [norm_sub_rev] using hh
    _ = (t ^ 2 + |t|) * ∑ n ∈ Ioc A N, ((n : ℝ) ^ 2)⁻¹ := by
      simp_rw [div_eq_mul_inv, mul_sum]
    _ ≤ (t ^ 2 + |t|) * ((A : ℝ)⁻¹ - (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by omega : A ≠ 0) hAN) (by positivity)
    _ ≤ (t ^ 2 + |t|) / A := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)

lemma halasz_power_phase_prefix_norm (t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ioc 0 N, halaszPowerPhase t n‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖halaszPowerPhase t n‖ := norm_sum_le _ _
    _ = _ := by simp

theorem halasz_power_phase_sum_integral (t : ℝ) (N : ℕ) :
    ‖(∑ n ∈ Ioc 0 N, halaszPowerPhase t n) -
      ∫ x in (0 : ℝ)..(N : ℝ), halaszPowerPhase t x‖ ≤ 8 * (1 + |t|) := by
  let A : ℕ := ⌈1 + |t|⌉₊
  have hAlo : 1 + |t| ≤ (A : ℝ) := Nat.le_ceil _
  have hAhi : (A : ℝ) < 2 + |t| := by
    have hh : (A : ℝ) < 1 + |t| + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hA1 : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith [abs_nonneg t])
  have hi (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :=
    halasz_power_phase_intervalIntegrable t a b ha hb
  have hb : ∀ M : ℕ,
      ‖(∑ n ∈ Ioc 0 M, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..(M : ℝ), halaszPowerPhase t x‖ ≤ 2 * M := by
    intro M
    calc
      _ ≤ ‖∑ n ∈ Ioc 0 M, halaszPowerPhase t n‖ +
          ‖∫ x in (0 : ℝ)..(M : ℝ), halaszPowerPhase t x‖ := norm_sub_le _ _
      _ ≤ (M : ℝ) + M := add_le_add (halasz_power_phase_prefix_norm t M)
        (by simpa using halasz_power_phase_integral_norm t 0 M)
      _ = _ := by ring
  by_cases hNA : N ≤ A
  · have hNr : (N : ℝ) ≤ A := by exact_mod_cast hNA
    exact (hb N).trans (by linarith [abs_nonneg t])
  · have hAN : A ≤ N := by omega
    have hs := sum_Ioc_consecutive (fun n : ℕ => halaszPowerPhase t n)
      (Nat.zero_le A) hAN
    have hj := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 ((A : ℝ) + 1 / 2) (by norm_num) (by positivity))
      (hi ((A : ℝ) + 1 / 2) ((N : ℝ) + 1 / 2) (by positivity) (by positivity))
    have hk := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 N (by norm_num) (by positivity))
      (hi N ((N : ℝ) + 1 / 2) (by positivity) (by positivity))
    have he : (∑ n ∈ Ioc 0 N, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..(N : ℝ), halaszPowerPhase t x =
        ((∑ n ∈ Ioc 0 A, halaszPowerPhase t n) -
          ∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x) +
        ((∑ n ∈ Ioc A N, halaszPowerPhase t n) -
          ∫ x in ((A : ℝ) + 1 / 2)..((N : ℝ) + 1 / 2), halaszPowerPhase t x) +
        ∫ x in (N : ℝ)..((N : ℝ) + 1 / 2), halaszPowerPhase t x := by
      rw [← hs]
      linear_combination hj - hk
    have hhead : ‖(∑ n ∈ Ioc 0 A, halaszPowerPhase t n) -
        ∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤ 2 * A + 1 / 2 := by
      calc
        _ ≤ ‖∑ n ∈ Ioc 0 A, halaszPowerPhase t n‖ +
            ‖∫ x in (0 : ℝ)..((A : ℝ) + 1 / 2), halaszPowerPhase t x‖ := norm_sub_le _ _
        _ ≤ (A : ℝ) + ((A : ℝ) + 1 / 2) := add_le_add (halasz_power_phase_prefix_norm t A)
          (by
            have hh := halasz_power_phase_integral_norm t 0 ((A : ℝ) + 1 / 2)
            rw [sub_zero, abs_of_nonneg (by positivity)] at hh
            exact hh)
        _ = _ := by ring
    have htail := halasz_phase_cell_sum_error t A N hA1 hAN (by linarith)
    have hend : ‖∫ x in (N : ℝ)..((N : ℝ) + 1 / 2), halaszPowerPhase t x‖ ≤ 1 / 2 := by
      simpa using halasz_power_phase_integral_norm t N ((N : ℝ) + 1 / 2)
    have hratio : (t ^ 2 + |t|) / (A : ℝ) ≤ |t| := by
      apply (div_le_iff₀ (by exact_mod_cast (show 0 < A by omega))).mpr
      have hm := mul_le_mul_of_nonneg_left hAlo (abs_nonneg t)
      nlinarith [sq_abs t]
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hhead htail)) hend)).trans
        (by linarith [abs_nonneg t])


theorem halasz_power_phase_sum_real (t x : ℝ) (hx : 0 ≤ x) :
    ‖(∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
      (x : ℂ) * halaszPowerPhase t x / (1 + (-t : ℂ) * Complex.I)‖ ≤
        9 * (1 + |t|) := by
  have hN : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hN' : x - (⌊x⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one x]
  have hj := intervalIntegral.integral_add_adjacent_intervals
    (halasz_power_phase_intervalIntegrable t 0 ⌊x⌋₊ (by norm_num) (by positivity))
    (halasz_power_phase_intervalIntegrable t ⌊x⌋₊ x (by positivity) hx)
  have he : (∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
      ∫ y in (0 : ℝ)..x, halaszPowerPhase t y =
      ((∑ n ∈ Icc 1 ⌊x⌋₊, halaszPowerPhase t n) -
        ∫ y in (0 : ℝ)..(⌊x⌋₊ : ℝ), halaszPowerPhase t y) -
      ∫ y in (⌊x⌋₊ : ℝ)..x, halaszPowerPhase t y := by
    rw [← hj]
    ring
  have hset : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext n; simp; omega
  have hh := halasz_power_phase_sum_integral t ⌊x⌋₊
  rw [← hset] at hh
  have ht : ‖∫ y in (⌊x⌋₊ : ℝ)..x, halaszPowerPhase t y‖ ≤ 1 := by
    apply (halasz_power_phase_integral_norm t ⌊x⌋₊ x).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hN)]
    exact hN'.le
  have h := ((norm_sub_le _ _).trans (add_le_add hh ht)).trans
    (show 8 * (1 + |t|) + 1 ≤ 9 * (1 + |t|) by linarith [abs_nonneg t])
  rw [← he, halasz_power_phase_integral t 0 x (by norm_num) hx] at h
  simpa using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszUnitRenormalization
namespace OAI

/-! Elementary near-twist renormalization using the absolute unit correction.
The power-sum error is uniform in the summation cutoff and linear in the twist. -/

namespace TwoPointCorrelations

open _root_.Finset



lemma halasz_power_phase_mul (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    halaszPowerPhase t (x * y) = halaszPowerPhase t x * halaszPowerPhase t y := by
  simp only [halaszPowerPhase, Real.log_mul hx.ne' hy.ne', mul_add,
    Complex.ofReal_add, add_mul, Complex.exp_add]


lemma halasz_phase_mean_hyperbola (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    halaszPhaseMean F t N = ∑ d ∈ Icc 1 N,
      halaszUnitCorrection F d * halaszPowerPhase t d *
        ∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m := by
  unfold halaszPhaseMean
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        halaszUnitCorrection F p.1 * halaszPowerPhase t (p.1 * p.2) := by
      apply sum_congr rfl
      intro n hn
      rw [halasz_unit_correction_divisor_sum F hF hF1 (mem_Icc.mp hn).1, sum_mul,
        Nat.sum_divisorsAntidiagonal (fun a b =>
          halaszUnitCorrection F a * halaszPowerPhase t (a * b))]
      apply sum_congr rfl
      intro d hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        halaszUnitCorrection F d * halaszPowerPhase t (d * m) :=
      (halasz_sum_divisorsAntidiagonal (fun d m =>
        halaszUnitCorrection F d * halaszPowerPhase t (d * m)) N).trans
          (halasz_hyperbola_rows (fun d m =>
            halaszUnitCorrection F d * halaszPowerPhase t (d * m)) N)
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [halasz_power_phase_mul t d m
        (by exact_mod_cast (mem_Icc.mp hd).1) (by exact_mod_cast (mem_Icc.mp hm).1)]
      ring

lemma halasz_phase_main_local (t : ℝ) (N d : ℕ) (hd : 0 < d) :
    halaszPowerPhase t d *
      (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
        (1 + (-t : ℂ) * Complex.I)) =
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * (N : ℂ) / d := by
  by_cases hN : N = 0
  · subst N; simp
  have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have he := halasz_power_phase_mul t d ((N : ℝ) / d) hdp (div_pos hNp hdp)
  rw [mul_div_cancel₀ _ hdp.ne'] at he
  push_cast
  rw [he]
  ring

theorem halasz_phase_mean_main_error (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N‖ ≤
      9 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  have he : halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N =
      ∑ d ∈ Icc 1 N, halaszUnitCorrection F d * halaszPowerPhase t d *
        ((∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
            (1 + (-t : ℂ) * Complex.I))) := by
    rw [halasz_phase_mean_hyperbola F hF hF1, halaszUnitMain, ← mul_assoc, mul_sum,
      ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    have hh := halasz_phase_main_local t N d (mem_Icc.mp hd).1
    calc
      _ = halaszUnitCorrection F d * halaszPowerPhase t d *
          (∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          halaszUnitCorrection F d *
            ((halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * (N : ℂ) / d) := by ring
      _ = _ := by rw [← hh]; ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d * halaszPowerPhase t d *
        ((∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
            (1 + (-t : ℂ) * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ * (9 * (1 + |t|)) := by
      apply sum_le_sum
      intro d hd
      have hh := halasz_power_phase_sum_real t ((N : ℝ) / d) (by positivity)
      rw [Nat.floor_div_natCast, Nat.floor_natCast] at hh
      simpa only [norm_mul, halasz_power_phase_norm, mul_one] using
        mul_le_mul_of_nonneg_left hh (norm_nonneg (halaszUnitCorrection F d))
    _ = _ := by rw [← sum_mul]; ring


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_phase_mean_main_error := @OAI.TwoPointCorrelations.halasz_phase_mean_main_error
