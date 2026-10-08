-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_mixed_mean_numeric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:31:52.575546+00:00
-- url     : https://prove2.me/submissions/9ab12267-497d-4d96-905f-05fa81117098

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogMean
namespace OAI

/-! Recover an ordinary mean from its logarithmically weighted sum.
The absolute error is at most N for a one-bounded sequence. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_sum_log_factorial (N : ℕ) :
    (∑ n ∈ Icc 1 N, Real.log (n : ℝ)) = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

lemma halasz_sum_log_gap (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (Real.log (N : ℝ) - Real.log (n : ℝ))) ≤ N := by
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc, halasz_sum_log_factorial]
  have hst := Stirling.le_log_factorial_stirling (Nat.ne_zero_of_lt hN)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.two_le_pi])
  simp only [Nat.add_sub_cancel] at *
  linarith

lemma halasz_logarithmic_sum_error (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Icc 1 N, f n) * (Real.log (N : ℝ) : ℂ) -
      ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)‖ ≤ (N : ℝ) := by
  let S := ∑ n ∈ Icc 1 N, f n
  let W := ∑ n ∈ Icc 1 N, f n * (Real.log (n : ℝ) : ℂ)
  have he : S * (Real.log (N : ℝ) : ℂ) - W =
      ∑ n ∈ Icc 1 N, f n * ((Real.log (N : ℝ) - Real.log (n : ℝ) : ℝ) : ℂ) := by
    dsimp [S, W]
    rw [sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply (sum_le_sum ?_).trans (halasz_sum_log_gap N hN)
  intro n hn
  have hn' := mem_Icc.mp hn
  have hlog : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact mul_le_of_le_one_left hlog (hf n hn'.1)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers
namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The modulus-one specialization of the prime-power series bounds
the finite hyperbola error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszPrimePowerWeight_nonneg (n : ℕ) : 0 ≤ halaszPrimePowerWeight n := by
  unfold halaszPrimePowerWeight
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma halaszPrimePowerWeight_summable :
    Summable (fun n : ℕ => halaszPrimePowerWeight n / (n : ℝ)) := by
  have hh := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (0 : ZMod 1)
  convert (preTransparency := .instances) hh using 1
  funext n
  simp only [halaszPrimePowerWeight, ArithmeticFunction.vonMangoldt.residueClass]
  have he : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [he]


lemma halaszPrimePowerConstant_nonneg : 0 ≤ halaszPrimePowerConstant :=
  tsum_nonneg (fun n => div_nonneg (halaszPrimePowerWeight_nonneg n) (Nat.cast_nonneg _))

lemma halasz_bounded_prefix_norm (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) :=
      sum_le_sum (fun n hn => hf n (mem_Icc.mp hn).1)
    _ = _ := by simp


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



theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert (preTransparency := .instances) MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]


theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]



theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring








theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]


lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! (preTransparency := .instances) HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (preTransparency := .instances) (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! (preTransparency := .instances) Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (preTransparency := .instances) (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! (preTransparency := .instances) summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! (preTransparency := .instances) summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl


theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply Real.log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
namespace OAI

/-! Mertens' second theorem in bounded-error form.

The formal proof uses `Erdos970.Mertens.sum_prime_div_eq_log_log`.
Only the convention for the finite prime set differs from
`PrimeReciprocalInput`; zero contributes no prime to either convention.
-/

namespace TwoPointCorrelations

open _root_.Finset

lemma sievePrimesUpTo_eq_Ioc (x : ℝ) :
    sievePrimesUpTo x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [sievePrimesUpTo, mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨hp, hprime⟩
    exact ⟨⟨hprime.pos, hp⟩, hprime⟩
  · rintro ⟨⟨_, hp⟩, hprime⟩
    exact ⟨hp, hprime⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeBands
namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The reciprocal-mass bounds follow from Mertens’ theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mrt_sievePrimesUpTo_mono {P Q : ℝ} (hPQ : P ≤ Q) :
    sievePrimesUpTo P ⊆ sievePrimesUpTo Q := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hprime⟩
  exact mem_filter.mpr ⟨mem_Iic.mpr ((mem_Iic.mp hp).trans (Nat.floor_mono hPQ)), hprime⟩

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass
namespace OAI

/-! Mertens' first theorem, in the prime-band convention needed for the
small- and large-prime truncations in the Halasz convolution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halaszMertensConstant_nonneg : 0 ≤ halaszMertensConstant := by
  unfold halaszMertensConstant
  positivity

lemma halasz_prime_prefix_mass {x : ℝ} (hx : 1 ≤ x) :
    |(∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) - Real.log x| ≤
      halaszMertensConstant := by
  rw [sievePrimesUpTo_eq_Ioc]
  exact Erdos970.Mertens.sum_log_prime_div_eq_log hx

lemma halasz_prime_band_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) =
      (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
        ∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => Real.log (p : ℝ) / p)
    (mrt_sievePrimesUpTo_mono hPQ)

lemma halasz_prime_band_mertens {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    |(∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) -
        (Real.log Q - Real.log P)| ≤ 2 * halaszMertensConstant := by
  rw [halasz_prime_band_mass hPQ]
  have he : (∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) -
      (∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) -
      (Real.log Q - Real.log P) =
      ((∑ p ∈ sievePrimesUpTo Q, Real.log (p : ℝ) / p) - Real.log Q) -
      ((∑ p ∈ sievePrimesUpTo P, Real.log (p : ℝ) / p) - Real.log P) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by
    linarith [halasz_prime_prefix_mass hP, halasz_prime_prefix_mass (hP.trans hPQ)])

lemma halasz_prime_prefix_mass_le {x : ℝ} (hx : 1 ≤ x) :
    (∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p) ≤
      Real.log x + halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_prefix_mass hx)).2]

lemma halasz_prime_band_mass_le {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, Real.log (p : ℝ) / p) ≤
      Real.log Q - Real.log P + 2 * halaszMertensConstant := by
  linarith [(abs_le.mp (halasz_prime_band_mertens hP hPQ)).2]

lemma halasz_upper_half_prime_mass {x : ℝ} (hx : 2 ≤ x) :
    (∑ p ∈ mrtPrimeBand (x / 2) x, Real.log (p : ℝ) / p) ≤
      Real.log 2 + 2 * halaszMertensConstant := by
  have hx0 : 0 < x := by linarith
  have hm := halasz_prime_band_mass_le (P := x / 2) (Q := x)
    (by linarith) (by linarith)
  rw [Real.log_div (ne_of_gt hx0) (by norm_num)] at hm
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePartialSummation
namespace OAI

/-! Partial summation centered at Mertens' logarithmic main term. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical


lemma halasz_prime_weight_prefix (x : ℝ) :
    partialCoefficientSum halaszPrimeWeight x =
      ∑ p ∈ sievePrimesUpTo x, Real.log (p : ℝ) / p := by
  have he : Icc 0 ⌊x⌋₊ = Iic ⌊x⌋₊ := by ext n; simp
  simp only [partialCoefficientSum, he, sievePrimesUpTo, halaszPrimeWeight, sum_filter]

lemma halasz_prime_weight_band (f : ℝ → ℝ) {a b : ℝ} :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f n * halaszPrimeWeight n := by
  have he : mrtPrimeBand a b = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
    ext n
    simp only [mrtPrimeBand, sievePrimesUpTo, mem_sdiff, mem_filter, mem_Iic, mem_Ioc]
    by_cases hn : n.Prime <;> simp [hn, not_le, and_comm]
  rw [he, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : n.Prime <;> simp [halaszPrimeWeight, hn]

theorem halasz_prime_partial_summation (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∑ p ∈ mrtPrimeBand a b, f p * (Real.log (p : ℝ) / p)) -
        (∫ t in a..b, f t / t) =
      f b * (partialCoefficientSum halaszPrimeWeight b - Real.log b) -
      f a * (partialCoefficientSum halaszPrimeWeight a - Real.log a) -
      ∫ t in a..b, deriv f t *
        (partialCoefficientSum halaszPrimeWeight t - Real.log t) := by
  have hxn : ∀ x ∈ Set.Icc a b, x ≠ 0 := fun x hx => (ha.trans_le hx.1).ne'
  have hclog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdfi : IntervalIntegrable (deriv f) volume a b := hdf.intervalIntegrable_of_Icc hab
  have hlogi : IntervalIntegrable (fun x : ℝ => x⁻¹) volume a b :=
    (continuousOn_id.inv₀ hxn).intervalIntegrable_of_Icc hab
  have hfi : IntervalIntegrable (fun x => f x / x) volume a b :=
    (hfc.div continuousOn_id hxn).intervalIntegrable_of_Icc hab
  have hdmain : IntervalIntegrable (fun x => deriv f x * Real.log x) volume a b :=
    (hdf.mul hclog).intervalIntegrable_of_Icc hab
  have hsum : IntervalIntegrable
      (fun t => deriv f t * partialCoefficientSum halaszPrimeWeight t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc halaszPrimeWeight ha.le hdf.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul halaszPrimeWeight ha.le hab hf
    hdf.integrableOn_Icc
  rw [← intervalIntegral.integral_of_le hab, ← halasz_prime_weight_band f] at hAbel
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => (hf x (by simpa [Set.uIcc_of_le hab] using hx)).hasDerivAt)
    (fun x hx => Real.hasDerivAt_log (hxn x (by simpa [Set.uIcc_of_le hab] using hx)))
    hdfi hlogi
  have hsplit : (∫ t in a..b, deriv f t * Real.log t + f t * t⁻¹) =
      (∫ t in a..b, deriv f t * Real.log t) + ∫ t in a..b, f t / t := by
    simp only [← div_eq_mul_inv]
    exact intervalIntegral.integral_add hdmain hfi
  rw [hsplit] at hparts
  have herr : (∫ t in a..b, deriv f t *
      (partialCoefficientSum halaszPrimeWeight t - Real.log t)) =
      (∫ t in a..b, deriv f t * partialCoefficientSum halaszPrimeWeight t) -
      ∫ t in a..b, deriv f t * Real.log t := by
    simp only [mul_sub]
    exact intervalIntegral.integral_sub hsum hdmain
  rw [herr, hAbel]
  dsimp [partialCoefficientSum] at *
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDenominatorCalculus
namespace OAI

/-! Calculus for the variable denominator in the second prime convolution. -/

namespace TwoPointCorrelations

open _root_.MeasureTheory


lemma halasz_log_gap_pos {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    0 < Real.log X - Real.log x := sub_pos.mpr (Real.log_lt_log hx hxX)

lemma halasz_denominator_hasDerivAt {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (halaszDenominatorWeight X)
      (x⁻¹ / (Real.log X - Real.log x) ^ 2) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := hg.inv (ne_of_gt (halasz_log_gap_pos hx hxX))
  convert (preTransparency := .instances) hd using 1
  · rfl
  · simp only [Pi.sub_apply, zero_sub, neg_neg]

lemma halasz_denominator_primitive {X x : ℝ} (hx : 0 < x) (hxX : x < X) :
    HasDerivAt (fun y => -Real.log (Real.log X - Real.log y))
      (halaszDenominatorWeight X x / x) x := by
  have hg := (hasDerivAt_const x (Real.log X)).sub (Real.hasDerivAt_log hx.ne')
  have hd := ((Real.hasDerivAt_log (ne_of_gt (halasz_log_gap_pos hx hxX))).comp x hg).neg
  convert (preTransparency := .instances) hd using 1
  · rfl
  · simp only [zero_sub, halaszDenominatorWeight]
    ring

lemma halasz_denominator_deriv_continuous {X a b : ℝ} (ha : 0 < a)
    (hbX : b < X) : ContinuousOn (deriv (halaszDenominatorWeight X)) (Set.Icc a b) := by
  have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
    (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
  apply ContinuousOn.congr (f := fun x => x⁻¹ / (Real.log X - Real.log x) ^ 2)
  · exact (continuousOn_id.inv₀ hxn).div
      ((continuousOn_const.sub hlog).pow 2) (fun x hx => pow_ne_zero 2 (hgap x hx))
  · intro x hx
    exact (halasz_denominator_hasDerivAt (ha.trans_le hx.1) (hx.2.trans_lt hbX)).deriv

lemma halasz_denominator_integral {X a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbX : b < X) :
    (∫ t in a..b, halaszDenominatorWeight X t / t) =
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) := by
  have hf : ContinuousOn (fun t => halaszDenominatorWeight X t / t) (Set.Icc a b) := by
    have hxn (x : ℝ) (hx : x ∈ Set.Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
    have hgap (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log X - Real.log x ≠ 0 :=
      (halasz_log_gap_pos (ha.trans_le hx.1) (hx.2.trans_lt hbX)).ne'
    have hlog : ContinuousOn Real.log (Set.Icc a b) :=
      fun x hx => (Real.continuousAt_log (hxn x hx)).continuousWithinAt
    exact ((continuousOn_const.sub hlog).inv₀ hgap).div continuousOn_id hxn
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => halasz_denominator_primitive
      (ha.trans_le (show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).1)
      ((show x ∈ Set.Icc a b from by simpa [Set.uIcc_of_le hab] using hx).2.trans_lt hbX))
    (hf.intervalIntegrable_of_Icc hab)
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDenominatorMass
namespace OAI

/-! The weighted prime mass left by the second logarithmic convolution is
only of order log log X, with an absolute constant. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.MeasureTheory
open scoped _root_.Classical

lemma halasz_denominator_prime_error {X a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hbX : b < X) :
    (∑ p ∈ mrtPrimeBand a b,
      halaszDenominatorWeight X p * (Real.log (p : ℝ) / p)) ≤
      Real.log (Real.log X - Real.log a) - Real.log (Real.log X - Real.log b) +
        2 * halaszMertensConstant * halaszDenominatorWeight X b := by
  let w := halaszDenominatorWeight X
  let E := fun x => partialCoefficientSum halaszPrimeWeight x - Real.log x
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hxpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 < x := ha0.trans_le hx.1
  have hxX (x : ℝ) (hx : x ∈ Set.Icc a b) : x < X := hx.2.trans_lt hbX
  have hwpos (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ w x :=
    inv_nonneg.mpr (halasz_log_gap_pos (hxpos x hx) (hxX x hx)).le
  have hE (x : ℝ) (hx : x ∈ Set.Icc a b) : |E x| ≤ halaszMertensConstant := by
    dsimp [E]
    rw [halasz_prime_weight_prefix]
    exact halasz_prime_prefix_mass (ha.trans hx.1)
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt w (deriv w x) x :=
    (halasz_denominator_hasDerivAt (hxpos x hx) (hxX x hx)).differentiableAt.hasDerivAt
  have hdc : ContinuousOn (deriv w) (Set.Icc a b) :=
    halasz_denominator_deriv_continuous ha0 hbX
  have hdi : IntervalIntegrable (deriv w) volume a b := hdc.intervalIntegrable_of_Icc hab
  have hint : (∫ x in a..b, deriv w x) = w b - w a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x (by simpa [Set.uIcc_of_le hab] using hx)) hdi
  have hi : |∫ x in a..b, deriv w x * E x| ≤ halaszMertensConstant * (w b - w a) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x => deriv w x * E x) (g := fun x => halaszMertensConstant * deriv w x) hab
      (Filter.Eventually.of_forall (fun x hx => by
        have hxi : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2⟩
        have hd0 : 0 ≤ deriv w x := by
          rw [(halasz_denominator_hasDerivAt (hxpos x hxi) (hxX x hxi)).deriv]
          exact div_nonneg (inv_nonneg.mpr (hxpos x hxi).le) (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd0]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hE x hxi) hd0))
      (hdi.const_mul halaszMertensConstant)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, hint] at hb
    exact hb
  have hAbel := halasz_prime_partial_summation a b ha0 hab w
    (fun x hx => (hd x hx).differentiableAt) hdc
  rw [halasz_denominator_integral ha0 hab hbX] at hAbel
  change _ = w b * E b - w a * E a - _ at hAbel
  have heb := mul_le_mul_of_nonneg_left (abs_le.mp (hE b ⟨hab, le_rfl⟩)).2
    (hwpos b ⟨hab, le_rfl⟩)
  have hea := mul_le_mul_of_nonneg_left (abs_le.mp (hE a ⟨le_rfl, hab⟩)).1
    (hwpos a ⟨le_rfl, hab⟩)
  have hilow := (abs_le.mp hi).1
  dsimp [w] at *
  linarith

theorem halasz_denominator_prime_mass {X L : ℝ} (hL : 1 ≤ L) (hLX : L ≤ X / 2) :
    (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) ≤
      Real.log (Real.log X) - Real.log (Real.log 2) +
        2 * halaszMertensConstant / Real.log 2 := by
  have hX : 2 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hhX : X / 2 < X := by linarith
  have he : Real.log X - Real.log (X / 2) = Real.log 2 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hgap := halasz_log_gap_pos hL0 (lt_of_le_of_lt hLX hhX)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmain := Real.log_le_log hgap (show Real.log X - Real.log L ≤ Real.log X by linarith)
  have hb := halasz_denominator_prime_error hL hLX hhX
  have hsum : (∑ p ∈ mrtPrimeBand L (X / 2),
      Real.log (p : ℝ) / ((p : ℝ) * Real.log (X / p))) =
      ∑ p ∈ mrtPrimeBand L (X / 2),
        halaszDenominatorWeight X p * (Real.log (p : ℝ) / p) := by
    apply sum_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mrtPrimeBand_prime hp).pos
    rw [Real.log_div hX0.ne' hp0.ne', halaszDenominatorWeight]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsum]
  dsimp [halaszDenominatorWeight]
  simp only [halaszDenominatorWeight, he, ← div_eq_mul_inv] at hb
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleConvolution
namespace OAI

/-! Apply the prime convolution a second time, retaining the varying
denominator log(N/p). This is the adaptive triple sum in the short proof of
Halasz's theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma halasz_divisor_cutoff {N p : ℕ} (hp : 0 < p) (hpN : 2 * p ≤ N) :
    1 ≤ N / p ∧ ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p ∧
      (N : ℝ) / p ≤ 2 * ((N / p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hM : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
  refine ⟨hM, ?_, ?_⟩
  · apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  · have hmod : ((N % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt N hp
    have hid : ((N % p : ℕ) : ℝ) + (p : ℝ) * ((N / p : ℕ) : ℝ) = N := by
      exact_mod_cast Nat.mod_add_div N p
    have hM1 : (1 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hM
    apply (div_le_iff₀ hp0).mpr
    nlinarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedConvolution
namespace OAI

/-! Logarithmic convolution for a typical coefficient. Only multiplication
by primes above the deleted bands is used. The prime coefficient and the
remaining typical coefficient are kept distinct. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma halasz_raw_logarithmic_sum (B : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) =
      ∑ d ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt d:ℂ)*
        ∑ m ∈ Icc 1 (N/d), B (d*m) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.vonMangoldt p.1:ℂ)*B (p.1*p.2) := by
      apply sum_congr rfl
      intro n _
      rw [Nat.sum_divisorsAntidiagonal (fun a b =>
        (ArithmeticFunction.vonMangoldt a:ℂ)*B (a*b))]
      have he : (∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d:ℂ)*B n) =
          B n*(Real.log (n:ℝ):ℂ) := by
        rw [← sum_mul, ← Complex.ofReal_sum, ArithmeticFunction.vonMangoldt_sum]
        ring
      rw [← he]
      apply sum_congr rfl
      intro d hd
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    _ = ∑ p ∈ halaszHyperbola N,
        (ArithmeticFunction.vonMangoldt p.1:ℂ)*B (p.1*p.2) :=
      halasz_sum_divisorsAntidiagonal
        (fun a b => (ArithmeticFunction.vonMangoldt a:ℂ)*B (a*b)) N
    _ = _ := by
      rw [halasz_hyperbola_rows
        (fun a b => (ArithmeticFunction.vonMangoldt a:ℂ)*B (a*b)) N]
      apply sum_congr rfl
      intro d _
      rw [mul_sum]

lemma halasz_raw_row_bound (B : ℕ → ℂ) (hB : OneBounded B)
    (N d : ℕ) (hd : 0 < d) :
    ‖∑ m ∈ Icc 1 (N/d), B (d*m)‖ ≤ (N:ℝ)/d := by
  have hdiv : ((N/d:ℕ):ℝ) ≤ (N:ℝ)/d := by
    apply (le_div_iff₀ (show (0:ℝ)< d by exact_mod_cast hd)).mpr
    exact_mod_cast Nat.div_mul_le_self N d
  calc
    _ ≤ ∑ _m ∈ Icc 1 (N/d), (1:ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum (fun m hm =>
        hB (d*m) (Nat.mul_pos hd (mem_Icc.mp hm).1)))
    _ = ((N/d:ℕ):ℝ) := by simp
    _ ≤ _ := hdiv

lemma halasz_raw_prime_term_bound (B : ℕ → ℂ) (hB : OneBounded B)
    (N p : ℕ) (hp : p.Prime) :
    ‖halaszRawPrimeTerm B N p‖ ≤ (N:ℝ)*(Real.log (p:ℝ)/p) := by
  have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [halaszRawPrimeTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hl]
  calc
    _ ≤ Real.log (p:ℝ)*((N:ℝ)/p) :=
      mul_le_mul_of_nonneg_left (halasz_raw_row_bound B hB N p hp.pos) hl
    _ = _ := by ring

lemma halasz_raw_prime_power_error (B : ℕ → ℂ) (hB : OneBounded B) (N : ℕ) :
    ‖(∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p‖ ≤
        (N:ℝ)*halaszPrimePowerConstant := by
  rw [halasz_raw_logarithmic_sum, sum_filter, ← sum_sub_distrib]
  have he (d:ℕ) : (ArithmeticFunction.vonMangoldt d:ℂ)*
      (∑ m ∈ Icc 1 (N/d), B (d*m)) -
      (if d.Prime then halaszRawPrimeTerm B N d else 0) =
      (halaszPrimePowerWeight d:ℂ)*(∑ m ∈ Icc 1 (N/d), B (d*m)) := by
    by_cases hd : d.Prime
    · simp [hd,halaszRawPrimeTerm,halaszPrimePowerWeight,
        ArithmeticFunction.vonMangoldt_apply_prime hd]
    · simp [hd,halaszPrimePowerWeight]
  simp_rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N:ℝ)*(halaszPrimePowerWeight d/d) := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d hd
      have hw := halaszPrimePowerWeight_nonneg d
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      calc
        _ ≤ halaszPrimePowerWeight d*((N:ℝ)/d) :=
          mul_le_mul_of_nonneg_left
            (halasz_raw_row_bound B hB N d (mem_Icc.mp hd).1) hw
        _ = _ := by ring
    _ = (N:ℝ)*∑ d ∈ Icc 1 N, halaszPrimePowerWeight d/d := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halaszPrimePowerWeight_summable.sum_le_tsum _
        (fun d _ => div_nonneg (halaszPrimePowerWeight_nonneg d) (Nat.cast_nonneg d)))
      (Nat.cast_nonneg N)

lemma halasz_raw_prime_band_error (B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ N) :
    ‖(∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p) -
      ∑ p ∈ mrtPrimeBand L N, halaszRawPrimeTerm B N p‖ ≤
        (N:ℝ)*(Real.log L+halaszMertensConstant) := by
  have hnat : (Icc 1 N).filter Nat.Prime = sievePrimesUpTo (N:ℝ) := by
    ext p
    simp only [mem_filter,mem_Icc,sievePrimesUpTo,Nat.floor_natCast,mem_Iic]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩⟩
  rw [hnat, mrtPrimeBand, sum_sdiff_eq_sub (mrt_sievePrimesUpTo_mono hLN),
    sub_sub_cancel]
  calc
    _ ≤ (N:ℝ)*∑ p ∈ sievePrimesUpTo L, Real.log (p:ℝ)/p := by
      rw [mul_sum]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun p hp =>
        halasz_raw_prime_term_bound B hB N p (sievePrimesUpTo_prime L p hp)))
    _ ≤ _ := mul_le_mul_of_nonneg_left (halasz_prime_prefix_mass_le hL) (Nat.cast_nonneg N)

theorem halasz_mixed_logarithmic_approximation (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) {L : ℝ} (hL : 1 ≤ L) (hLN : L ≤ N)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖(∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (N:ℝ)*(halaszPrimePowerConstant+Real.log L+halaszMertensConstant) := by
  have hmixed : (∑ p ∈ mrtPrimeBand L N, halaszRawPrimeTerm B N p) =
      halaszMixedPrimeConvolution G B N L N := by
    unfold halaszMixedPrimeConvolution halaszRawPrimeTerm
    apply sum_congr rfl
    intro p hp
    have hpl := (mrtPrimeBand_bounds (by linarith) (Nat.cast_nonneg N) hp).1
    rw [mul_assoc]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    exact hmul p (mrtPrimeBand_prime hp) hpl m (mem_Icc.mp hm).1
  have hp := halasz_raw_prime_power_error B hB N
  have hl := halasz_raw_prime_band_error B hB N hL hLN
  rw [hmixed] at hl
  have hh := norm_add_le
    ((∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p)
    ((∑ p ∈ (Icc 1 N).filter Nat.Prime, halaszRawPrimeTerm B N p) -
      halaszMixedPrimeConvolution G B N L N)
  rw [sub_add_sub_cancel] at hh
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedInner
namespace OAI

/-! The inner logarithmic approximation for the actual typical sequence.
The same estimate covers cofactors shorter than the deleted-prime cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_mixed_logarithmic_approximation_all (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (_hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖(∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (N:ℝ)*(halaszPrimePowerConstant+Real.log L+halaszMertensConstant) := by
  by_cases hLN : L ≤ (N:ℝ)
  · exact halasz_mixed_logarithmic_approximation G B hB N hL hLN hmul
  have hNL : (N:ℝ) < L := lt_of_not_ge hLN
  have hempty : mrtPrimeBand L N = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hb := mrtPrimeBand_bounds (by linarith : 0 ≤ L) (Nat.cast_nonneg N) hp
    linarith
  simp only [halaszMixedPrimeConvolution,hempty,sum_empty,sub_zero]
  have hc := halaszPrimePowerConstant_nonneg
  have hm := halaszMertensConstant_nonneg
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  calc
    _ ≤ ∑ n ∈ Icc 1 N, Real.log L := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hln]
      apply (mul_le_of_le_one_left hln (hB n hn1)).trans
      apply Real.log_le_log (by exact_mod_cast hn1)
      exact (show (n:ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn).2).trans hNL.le
    _ = (N:ℝ)*Real.log L := by simp
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α:=ℝ) N]

lemma halasz_mixed_prefix_log (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖(∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1)*(N:ℝ) := by
  have he := halasz_logarithmic_sum_error B hB N hN
  have hp := halasz_mixed_logarithmic_approximation_all G B hB N hN hL hmul
  have ht := norm_add_le
    ((∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
      ∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ))
    ((∑ n ∈ Icc 1 N, B n*(Real.log (n:ℝ):ℂ)) -
      halaszMixedPrimeConvolution G B N L N)
  rw [sub_add_sub_cancel] at ht
  nlinarith

lemma halasz_mixed_real_log_approximation (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m)
    {x : ℝ} (hNx : (N:ℝ) ≤ x) (hxN : x ≤ 2*N) :
    ‖(∑ n ∈ Icc 1 N, B n)*(Real.log x:ℂ) -
      halaszMixedPrimeConvolution G B N L N‖ ≤
        (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2)*x := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := hN0.trans_le hNx
  have hgap0 : 0 ≤ Real.log x-Real.log (N:ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hN0 hNx)
  have hgap2 : Real.log x-Real.log (N:ℝ) ≤ Real.log 2 := by
    have hh := Real.log_le_log hx0 hxN
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN0.ne'] at hh
    linarith
  have he : (∑ n ∈ Icc 1 N, B n)*(Real.log x:ℂ) -
      halaszMixedPrimeConvolution G B N L N =
      (∑ n ∈ Icc 1 N, B n)*((Real.log x-Real.log (N:ℝ):ℝ):ℂ) +
      ((∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
        halaszMixedPrimeConvolution G B N L N) := by push_cast; ring
  have hC : 0 ≤ halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2 := by
    have := halaszPrimePowerConstant_nonneg
    have := halaszMertensConstant_nonneg
    have := Real.log_nonneg hL
    positivity
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ Icc 1 N, B n)*((Real.log x-Real.log (N:ℝ):ℝ):ℂ)‖ +
        ‖(∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ) -
          halaszMixedPrimeConvolution G B N L N‖ := norm_add_le _ _
    _ ≤ (N:ℝ)*Real.log 2 +
        (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1)*(N:ℝ) := by
      apply add_le_add _ (halasz_mixed_prefix_log G B hB N hN hL hmul)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hgap0]
      exact mul_le_mul (halasz_bounded_prefix_norm B hB N) hgap2 hgap0 (Nat.cast_nonneg N)
    _ = (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2)*(N:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hNx hC

lemma halasz_mixed_real_inner_approximation (G B : ℕ → ℂ) (hB : OneBounded B)
    (N : ℕ) (hN : 1 ≤ N) {L : ℝ} (hL : 1 ≤ L)
    (hmul : ∀ p : ℕ, p.Prime → L < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m)
    {x : ℝ} (hx : 1 < x) (hNx : (N:ℝ) ≤ x) (hxN : x ≤ 2*N) :
    ‖(∑ n ∈ Icc 1 N, B n) - halaszMixedPrimeConvolution G B N L N/(Real.log x:ℂ)‖ ≤
      (halaszPrimePowerConstant+Real.log L+halaszMertensConstant+1+Real.log 2)*x/Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogC : (Real.log x:ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have he : (∑ n ∈ Icc 1 N, B n) - halaszMixedPrimeConvolution G B N L N/(Real.log x:ℂ) =
      ((∑ n ∈ Icc 1 N, B n)*(Real.log x:ℂ) -
        halaszMixedPrimeConvolution G B N L N)/(Real.log x:ℂ) := by field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right
    (halasz_mixed_real_log_approximation G B hB N hN hL hmul hNx hxN) hlog.le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedBounds
namespace OAI

/-! Trivial estimates for the mixed prime convolution. The underlying
prime values and the bounded typical cofactor are different sequences. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical


lemma halasz_mixed_prime_term_bound (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N p : ℕ) (hp : p.Prime) :
    ‖(Real.log (p:ℝ):ℂ)*G p*(∑ m ∈ Icc 1 (N/p), B m)‖ ≤
      (N:ℝ)*(Real.log (p:ℝ)/p) := by
  have hp0 : (0:ℝ)< p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hdiv : ((N/p:ℕ):ℝ) ≤ (N:ℝ)/p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p:ℝ)*1*((N/p:ℕ):ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hG p hp.pos) hlog)
        (halasz_bounded_prefix_norm B hB (N/p)) (norm_nonneg _) (by positivity)
    _ ≤ Real.log (p:ℝ)*((N:ℝ)/p) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hlog
    _ = _ := by ring




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedDouble
namespace OAI

/-! Two logarithmic convolutions with a prime cutoff above every selected
typical band. No multiplicativity of the typical coefficient is asserted. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma halasz_mixed_error_nonneg {R : ℝ} (hR : 1 ≤ R) :
    0 ≤ halaszMixedErrorConstant R := by
  have := halaszPrimePowerConstant_nonneg
  have := halaszMertensConstant_nonneg
  have := Real.log_nonneg hR
  unfold halaszMixedErrorConstant
  positivity

theorem halasz_mixed_double_error (G B : ℕ → ℂ) (hG : OneBounded G) (hB : OneBounded B)
    (N : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    ‖halaszMixedPrimeConvolution G B N R ((N:ℝ)/2)-halaszMixedDouble G B N R‖ ≤
      halaszMixedErrorConstant R*(N:ℝ)*∑ p ∈ mrtPrimeBand R ((N:ℝ)/2),
        Real.log (p:ℝ)/((p:ℝ)*Real.log ((N:ℝ)/p)) := by
  unfold halaszMixedPrimeConvolution halaszMixedDouble halaszMixedGrouped
  rw [← sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  have hprime := mrtPrimeBand_prime hp
  have hb := mrtPrimeBand_bounds (by linarith : 0 ≤ R) (by positivity : (0:ℝ)≤(N:ℝ)/2) hp
  have hpN : 2*p ≤ N := by exact_mod_cast (show 2*(p:ℝ)≤ N by linarith)
  obtain ⟨hM,hMx,hxM⟩ := halasz_divisor_cutoff hprime.pos hpN
  have hp0 : (0:ℝ)< p := by exact_mod_cast hprime.pos
  have hx : 1 < (N:ℝ)/p := by
    have hh : (2:ℝ)≤(N:ℝ)/p := (le_div_iff₀ hp0).mpr (by linarith)
    linarith
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  rw [← mul_sub,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p:ℝ)*1*(halaszMixedErrorConstant R*((N:ℝ)/p)/Real.log ((N:ℝ)/p)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hG p hprime.pos) hlog
      · exact halasz_mixed_real_inner_approximation G B hB (N/p) hM hR hmul hx hMx hxM
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

lemma halasz_mixed_upper_truncation (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2) :
    ‖halaszMixedPrimeConvolution G B N R N-
      halaszMixedPrimeConvolution G B N R ((N:ℝ)/2)‖ ≤
      (N:ℝ)*(Real.log 2+2*halaszMertensConstant) := by
  have hsub : mrtPrimeBand R ((N:ℝ)/2) ⊆ mrtPrimeBand R N := by
    apply sdiff_subset_sdiff_left
    exact mrt_sievePrimesUpTo_mono (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have he : mrtPrimeBand R N \ mrtPrimeBand R ((N:ℝ)/2) = mrtPrimeBand ((N:ℝ)/2) N := by
    ext p
    simp only [mrtPrimeBand,mem_sdiff]
    have hRsub := mrt_sievePrimesUpTo_mono hRN
    tauto
  unfold halaszMixedPrimeConvolution
  rw [← sum_sdiff hsub,he,add_sub_cancel_right]
  calc
    _ ≤ (N:ℝ)*∑ p ∈ mrtPrimeBand ((N:ℝ)/2) N, Real.log (p:ℝ)/p := by
      rw [mul_sum]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun p hp =>
        halasz_mixed_prime_term_bound G B hG hB N p (mrtPrimeBand_prime hp)))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halasz_upper_half_prime_mass (by linarith : (2:ℝ)≤ N)) (Nat.cast_nonneg N)

theorem halasz_mixed_double_mean (G B : ℕ → ℂ) (hG : OneBounded G) (hB : OneBounded B)
    (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2)
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖ ≤ ‖halaszMixedDouble G B N R‖ +
      (N:ℝ)*((halaszPrimePowerConstant+Real.log R+3*halaszMertensConstant+1+Real.log 2)+
        halaszMixedErrorConstant R*(Real.log (Real.log N)-Real.log (Real.log 2)+
          2*halaszMertensConstant/Real.log 2)) := by
  have hN : 1 ≤ N := by exact_mod_cast (show (1:ℝ)≤ N by linarith)
  have hp := halasz_mixed_prefix_log G B hB N hN hR hmul
  have hu := halasz_mixed_upper_truncation G B hG hB N hR hRN
  have hd := halasz_mixed_double_error G B hG hB N hR hmul
  have hm := mul_le_mul_of_nonneg_left (halasz_denominator_prime_mass hR hRN)
    (mul_nonneg (halasz_mixed_error_nonneg hR) (Nat.cast_nonneg N))
  have hn := norm_add_le (halaszMixedDouble G B N R)
    (halaszMixedPrimeConvolution G B N R ((N:ℝ)/2)-halaszMixedDouble G B N R)
  rw [add_sub_cancel] at hn
  have ht := norm_add_le (halaszMixedPrimeConvolution G B N R ((N:ℝ)/2))
    (halaszMixedPrimeConvolution G B N R N-halaszMixedPrimeConvolution G B N R ((N:ℝ)/2))
  rw [add_sub_cancel] at ht
  have hs := norm_add_le (halaszMixedPrimeConvolution G B N R N)
    ((∑ n ∈ Icc 1 N, B n)*(Real.log (N:ℝ):ℂ)-halaszMixedPrimeConvolution G B N R N)
  rw [add_sub_cancel,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))] at hs
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedNumeric
namespace OAI

/-! The cost of deleting primes below the upper endpoint of the typical
bands, before applying the mixed Perron estimate. -/

namespace TwoPointCorrelations

open _root_.Finset



lemma halasz_mixed_mean_numeric (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N : ℕ) {R : ℝ} (hR : 1 ≤ R) (hRN : R ≤ (N:ℝ)/2)
    (hll : 1 ≤ Real.log (Real.log (N:ℝ)))
    (hmul : ∀ p : ℕ, p.Prime → R < (p:ℝ) → ∀ m : ℕ, 0 < m → B (p*m)=G p*B m) :
    Real.log (N:ℝ)*‖∑ n ∈ Icc 1 N, B n‖ ≤ ‖halaszMixedDouble G B N R‖ +
      halaszMixedNumericConstant*(N:ℝ)*(1+Real.log R)*Real.log (Real.log N) := by
  have hh := halasz_mixed_double_mean G B hG hB N hR hRN hmul
  let A := halaszPrimePowerConstant+3*halaszMertensConstant+1+Real.log 2
  let E := halaszPrimePowerConstant+halaszMertensConstant+1+Real.log 2
  let r := Real.log R
  let l := Real.log (Real.log (N:ℝ))
  have hA : 0 ≤ A := by
    dsimp [A]
    have := halaszPrimePowerConstant_nonneg
    have := halaszMertensConstant_nonneg
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    have := halaszPrimePowerConstant_nonneg
    have := halaszMertensConstant_nonneg
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hr : 0 ≤ r := Real.log_nonneg hR
  have hl : 1 ≤ l := hll
  have hb : A+r ≤ (A+1)*(1+r)*l := by
    calc
      _ ≤ (A+1)*(1+r) := by nlinarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hl
  have he : E+r ≤ (E+1)*(1+r) := by nlinarith
  have hd : l+halaszDenominatorConstant ≤ (1+|halaszDenominatorConstant|)*l := by
    have ha := le_abs_self halaszDenominatorConstant
    have hb := le_mul_of_one_le_right (abs_nonneg halaszDenominatorConstant) hl
    nlinarith
  have hc : (E+r)*(l+halaszDenominatorConstant) ≤
      ((E+1)*(1+r))*((1+|halaszDenominatorConstant|)*l) := by
    calc
      _ ≤ (E+r)*((1+|halaszDenominatorConstant|)*l) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)
  have hs : A+r+(E+r)*(l+halaszDenominatorConstant) ≤
      halaszMixedNumericConstant*(1+r)*l := by
    dsimp [halaszMixedNumericConstant]
    change A+r+(E+r)*(l+halaszDenominatorConstant) ≤
      ((A+1)+(E+1)*(1+|halaszDenominatorConstant|))*(1+r)*l
    nlinarith
  have hn := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N : (0:ℝ)≤ N)
  dsimp [halaszMixedErrorConstant] at hh
  dsimp [A,E,r,l,halaszDenominatorConstant] at hn
  nlinarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_mixed_mean_numeric := @OAI.TwoPointCorrelations.halasz_mixed_mean_numeric
