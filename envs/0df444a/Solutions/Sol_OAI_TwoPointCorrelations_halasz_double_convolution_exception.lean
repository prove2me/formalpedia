-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_double_convolution_exception
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:33:20.981996+00:00
-- url     : https://prove2.me/submissions/84efe5f7-fe3b-4dbb-8eaf-f13cc65ec8ce

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_grouped_double_exception

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers
namespace OAI

/-! The total reciprocal contribution of higher prime powers is finite.
The modulus-one specialization of the prime-power series bounds
the finite hyperbola error. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszLogBands
namespace OAI

/-! Mertens weights on the geometric bands of log(X/p) in the adaptive
double convolution. The bounds remain valid for the last band near p=2. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_mem_prime_band {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p : ℕ} (hp : p.Prime) (hap : a < p) (hpb : (p : ℝ) ≤ b) :
    p ∈ mrtPrimeBand a b := by
  apply mem_sdiff.mpr
  constructor
  · exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hb).mpr hpb), hp⟩
  · intro h
    have hpa := (Nat.le_floor_iff ha).mp (mem_Iic.mp (mem_filter.mp h).1)
    linarith

lemma halasz_log_band_endpoints {X v : ℝ} (hX : 0 < X)
    {p : ℕ} (hp : p.Prime)
    (hlo : v ≤ Real.log (X / p)) (hhi : Real.log (X / p) < 2 * v) :
    X / Real.exp (2 * v) < p ∧ (p : ℝ) ≤ X / Real.exp v := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hxquot : 0 < X / p := div_pos hX hp0
  have hexlo : Real.exp v ≤ X / p := (Real.le_log_iff_exp_le hxquot).mp hlo
  have hexhi : X / p < Real.exp (2 * v) := (Real.log_lt_iff_lt_exp hxquot).mp hhi
  constructor
  · apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    have h := (div_lt_iff₀ hp0).mp hexhi
    nlinarith
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have h := (le_div_iff₀ hp0).mp hexlo
    nlinarith

theorem halasz_log_band_mass {X v : ℝ} (hX : 0 < X) (hv : 0 < v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧
      v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ v + 2 * halaszMertensConstant := by
  let a := max 1 (X / Real.exp (2 * v))
  let b := X / Real.exp v
  have hb0 : 0 < b := div_pos hX (Real.exp_pos _)
  by_cases hb : 1 ≤ b
  · have hlower : X / Real.exp (2 * v) ≤ b :=
      div_le_div_of_nonneg_left hX.le (Real.exp_pos _)
        (Real.exp_le_exp.mpr (by linarith))
    have ha : 1 ≤ a := le_max_left _ _
    have hab : a ≤ b := max_le hb hlower
    have hsub : P ⊆ mrtPrimeBand a b := by
      intro p hp
      obtain ⟨hprime, hlo, hhi⟩ := hP p hp
      obtain ⟨hpa, hpb⟩ := halasz_log_band_endpoints hX hprime hlo hhi
      exact halasz_mem_prime_band (by dsimp [a]; positivity) hb0.le hprime
        (max_lt (by exact_mod_cast hprime.one_lt) hpa) hpb
    have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) / p)
      hsub (fun p hp _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (mrtPrimeBand_prime hp).one_le))
        (Nat.cast_nonneg _))
    have hlog : Real.log b - Real.log a ≤ v := by
      have hloga : Real.log (X / Real.exp (2 * v)) ≤ Real.log a :=
        Real.log_le_log (div_pos hX (Real.exp_pos _)) (le_max_right _ _)
      rw [Real.log_div hX.ne' (Real.exp_ne_zero _), Real.log_exp] at hloga
      dsimp [b]
      rw [Real.log_div hX.ne' (Real.exp_ne_zero _), Real.log_exp]
      linarith
    exact hsum.trans ((halasz_prime_band_mass_le ha hab).trans (by linarith))
  · have hempty : P = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hprime, hlo, hhi⟩ := hP p hp
      have hpb := (halasz_log_band_endpoints hX hprime hlo hhi).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      linarith
    rw [hempty, sum_empty]
    exact add_nonneg hv.le (mul_nonneg (by norm_num) halaszMertensConstant_nonneg)

theorem halasz_log_band_mass_linear {X v : ℝ} (hX : 0 < X) (hv : Real.log 2 ≤ v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧
      v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) ≤
      (1 + 2 * halaszMertensConstant / Real.log 2) * v := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (halasz_log_band_mass hX (htwo.trans_le hv) P hP).trans
  have hm := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ 2 * halaszMertensConstant / Real.log 2 from
      div_nonneg (mul_nonneg (by norm_num) halaszMertensConstant_nonneg) htwo.le)
  rw [div_mul_cancel₀ _ htwo.ne'] at hm
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBandPartition
namespace OAI

/-! A finite geometric partition of log(X/p), using base-two bands. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma halasz_band_scale_bounds {y : ℝ} (hy : Real.log 2 ≤ y) :
    halaszBandScale (halaszBandIndex y) ≤ y ∧
      y < 2 * halaszBandScale (halaszBandIndex y) := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 ≤ y / Real.log 2 := div_nonneg (htwo.le.trans hy) htwo.le
  have hfloor : 1 ≤ ⌊y / Real.log 2⌋₊ :=
    (Nat.le_floor_iff hy0).mpr ((le_div_iff₀ htwo).mpr (by simpa using hy))
  have hlow := Nat.pow_log_le_self 2 (by omega : ⌊y / Real.log 2⌋₊ ≠ 0)
  have hhigh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊y / Real.log 2⌋₊
  have hlowR : (2 : ℝ) ^ halaszBandIndex y ≤ (⌊y / Real.log 2⌋₊ : ℝ) := by
    exact_mod_cast hlow
  have hhighR : (⌊y / Real.log 2⌋₊ : ℝ) + 1 ≤ (2 : ℝ) ^ (halaszBandIndex y + 1) := by
    exact_mod_cast hhigh
  constructor
  · have h := hlowR.trans (Nat.floor_le hy0)
    have hh := (le_div_iff₀ htwo).mp h
    simpa only [halaszBandScale, mul_comm] using hh
  · have h := (Nat.lt_floor_add_one (y / Real.log 2)).trans_le hhighR
    have hh := (div_lt_iff₀ htwo).mp h
    simpa only [halaszBandScale, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh

lemma halasz_band_index_mono {y Y : ℝ} (hyY : y ≤ Y) :
    halaszBandIndex y ≤ halaszBandIndex Y := by
  apply Nat.log_mono_right
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_right hyY (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))


lemma halasz_prime_band_part_bounds (P : Finset ℕ) {X : ℝ} {j p : ℕ}
    (hP : ∀ p ∈ P, Real.log 2 ≤ Real.log (X / p))
    (hp : p ∈ halaszPrimeBandPart P X j) :
    halaszBandScale j ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * halaszBandScale j := by
  obtain ⟨hpP, hpj⟩ := mem_filter.mp hp
  simpa only [hpj] using halasz_band_scale_bounds (hP p hpP)

theorem halasz_prime_band_partition (P : Finset ℕ) {X Y : ℝ}
    (hP : ∀ p ∈ P, Real.log (X / p) ≤ Y) (a : ℕ → ℂ) :
    (∑ p ∈ P, a p) =
      ∑ j ∈ range (halaszBandIndex Y + 1), ∑ p ∈ halaszPrimeBandPart P X j, a p := by
  symm
  apply sum_fiberwise_of_maps_to
  intro p hp
  exact mem_range.mpr (Nat.lt_succ_of_le (halasz_band_index_mono (hP p hp)))

lemma halasz_band_scale_ge_log_two (j : ℕ) : Real.log 2 ≤ halaszBandScale j := by
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  simpa only [mul_one, halaszBandScale] using
    mul_le_mul_of_nonneg_left hp (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBandSummation
namespace OAI

/-! Summing the minimum of the trivial band estimate and the distance
estimate. This is the step that keeps the factor (M+1) exp(-M). -/

namespace TwoPointCorrelations

open _root_.Finset

lemma halasz_band_scale_sum (J : ℕ) :
    (∑ j ∈ range J, halaszBandScale j) = Real.log 2 * ((2 : ℝ) ^ J - 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      simp only [halaszBandScale, pow_succ]
      ring

lemma halasz_band_scale_sum_le (J : ℕ) :
    (∑ j ∈ range J, halaszBandScale j) ≤ halaszBandScale J := by
  rw [halasz_band_scale_sum]
  dsimp [halaszBandScale]
  have htwo := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  nlinarith

lemma halasz_band_inverse_sum (J : ℕ) :
    (∑ j ∈ range J, (halaszBandScale j)⁻¹) =
      (2 / Real.log 2) * (1 - ((2 : ℝ)⁻¹) ^ J) := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [sum_range_succ, ih]
      simp only [halaszBandScale, mul_inv_rev, inv_pow, pow_succ]
      ring

lemma halasz_band_inverse_sum_le (J : ℕ) :
    (∑ j ∈ range J, (halaszBandScale j)⁻¹) ≤ 2 / Real.log 2 := by
  rw [halasz_band_inverse_sum]
  have htwo : 0 ≤ 2 / Real.log 2 := by positivity
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ J := by positivity
  nlinarith

lemma halasz_band_min_split {A : ℝ} (_hA : 0 ≤ A) (J k : ℕ) (hk : k ≤ J) :
    (∑ j ∈ range J, min A (halaszBandScale j)) ≤
      halaszBandScale k + (J - k : ℕ) * A := by
  rw [← sum_range_add_sum_Ico _ hk]
  have hfirst : (∑ j ∈ range k, min A (halaszBandScale j)) ≤ halaszBandScale k :=
    (sum_le_sum (fun j _ => min_le_right _ _)).trans (halasz_band_scale_sum_le k)
  have hlast : (∑ j ∈ Ico k J, min A (halaszBandScale j)) ≤ (J - k : ℕ) * A := by
    apply (sum_le_sum (fun j _ => min_le_left _ _)).trans_eq
    simp
  exact add_le_add hfirst hlast

theorem halasz_band_saving_sum : ∃ C : ℝ, 0 < C ∧
    ∀ (J : ℕ) (V M : ℝ), 0 ≤ V → 0 ≤ M → halaszBandScale J ≤ 2 * V →
      (∑ j ∈ range J, min (V * Real.exp (-M)) (halaszBandScale j)) ≤
        C * V * (M + 1) * Real.exp (-M) := by
  let C := 1 / Real.log 2 + 3
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro J V M hV hM htop
  let r : ℕ := ⌈M / Real.log 2⌉₊
  let A := V * Real.exp (-M)
  have hA : 0 ≤ A := mul_nonneg hV (Real.exp_pos _).le
  have hrlo : M / Real.log 2 ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < M / Real.log 2 + 1 := Nat.ceil_lt_add_one (div_nonneg hM htwo.le)
  have hpow : Real.exp M ≤ (2 : ℝ) ^ r := by
    have h := Real.exp_le_exp.mpr ((div_le_iff₀ htwo).mp hrlo)
    simpa only [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hsum : (∑ j ∈ range J, min A (halaszBandScale j)) ≤ ((r : ℝ) + 2) * A := by
    by_cases hrJ : r ≤ J
    · have hscale : halaszBandScale (J - r) ≤ 2 * A := by
        have hmul : halaszBandScale (J - r) * (2 : ℝ) ^ r = halaszBandScale J := by
          dsimp [halaszBandScale]
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hrJ]
        calc
          _ = halaszBandScale J / (2 : ℝ) ^ r := by rw [← hmul]; field_simp
          _ ≤ 2 * V / (2 : ℝ) ^ r := div_le_div_of_nonneg_right htop (by positivity)
          _ ≤ 2 * V / Real.exp M := div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hpow
          _ = 2 * A := by dsimp [A]; rw [Real.exp_neg]; ring
      have hs := halasz_band_min_split hA J (J - r) (Nat.sub_le _ _)
      have hcard : J - (J - r) = r := Nat.sub_sub_self hrJ
      rw [hcard] at hs
      nlinarith
    · have hcount : (J : ℝ) ≤ r := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hrJ))
      have hs : (∑ j ∈ range J, min A (halaszBandScale j)) ≤ (J : ℝ) * A := by
        apply (sum_le_sum (fun j _ => min_le_left _ _)).trans_eq
        simp
      nlinarith
  have hlinear : (r : ℝ) + 2 ≤ C * (M + 1) := by
    have hi : 0 ≤ 1 / Real.log 2 := by positivity
    dsimp [C]
    rw [div_eq_mul_inv] at hrhi
    simp only [one_div] at hi ⊢
    nlinarith
  calc
    _ ≤ ((r : ℝ) + 2) * A := hsum
    _ ≤ (C * (M + 1)) * A := mul_le_mul_of_nonneg_right hlinear hA
    _ = _ := by dsimp [A]; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeTruncation
namespace OAI

/-! The small- and large-prime deletion in the double-convolution argument.
All errors are uniform over one-bounded coefficients. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma halasz_prime_term_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N p : ℕ) (hp : p.Prime) :
    ‖halaszPrimeTerm f N p‖ ≤ (N : ℝ) * (Real.log (p : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hdiv : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  unfold halaszPrimeTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p : ℝ) * 1 * ((N / p : ℕ) : ℝ) := by
      gcongr
      · exact hf p hp.pos
      · exact halasz_bounded_prefix_norm f hf (N / p)
    _ ≤ Real.log (p : ℝ) * ((N : ℝ) / p) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hlog
    _ = _ := by ring

lemma halasz_prime_set_bound (f : ℕ → ℂ) (hf : OneBounded f)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ‖∑ p ∈ P, halaszPrimeTerm f N p‖ ≤
      (N : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  exact sum_le_sum (fun p hp => halasz_prime_term_bound f hf N p (hP p hp))







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszGroupedBounds
namespace OAI

/-! The complementary trivial estimate for a logarithmic prime band.
Together with the Perron estimate it produces the minimum summed later. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical


lemma halasz_prime_convolution_trivial (f : ℕ → ℂ) (hf : OneBounded f)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖halaszPrimeConvolution f N‖ ≤ (N : ℝ) * (Real.log N + halaszMertensConstant) := by
  have hp := halasz_prime_set_bound f hf N ((Icc 1 N).filter Nat.Prime)
    (fun p hp => (mem_filter.mp hp).2)
  have hs : (Icc 1 N).filter Nat.Prime = sievePrimesUpTo (N : ℝ) := by
    ext p
    simp only [sievePrimesUpTo, Nat.floor_natCast, mem_filter, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩⟩
  change ‖halaszPrimeConvolution f N‖ ≤ _ at hp
  rw [hs] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (halasz_prime_prefix_mass_le (by exact_mod_cast hN)) (Nat.cast_nonneg _))

lemma halasz_prime_convolution_div_log (f : ℕ → ℂ) (hf : OneBounded f)
    {M : ℕ} {y : ℝ} (hy : 2 ≤ y) (hMy : (M : ℝ) ≤ y) :
    ‖halaszPrimeConvolution f M / (Real.log y : ℂ)‖ ≤
      (1 + halaszMertensConstant / Real.log 2) * y := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : 0 < Real.log y := htwo.trans_le hlog
  have hMertens := halaszMertensConstant_nonneg
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hly]
  by_cases hM : M = 0
  · subst M
    simp only [halaszPrimeConvolution, Icc_eq_empty_of_lt (by omega : 0 < 1),
      filter_empty, sum_empty, norm_zero, zero_div]
    positivity
  · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    have hLM : Real.log (M : ℝ) ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hM)) hMy
    calc
      _ ≤ ((M : ℝ) * (Real.log M + halaszMertensConstant)) / Real.log y :=
        div_le_div_of_nonneg_right (halasz_prime_convolution_trivial f hf hM1) hly.le
      _ ≤ (y * (Real.log y + halaszMertensConstant)) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hly.le
        exact mul_le_mul hMy (add_le_add hLM le_rfl)
          (add_nonneg (Real.log_nonneg (by exact_mod_cast hM1)) hMertens) (by linarith)
      _ = (1 + halaszMertensConstant / Real.log y) * y := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact add_le_add le_rfl (div_le_div_of_nonneg_left hMertens htwo hlog)

theorem halasz_grouped_double_trivial : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (N : ℕ) (v : ℝ), 0 < N → Real.log 2 ≤ v →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      ‖halaszGroupedDouble f N P‖ ≤ C * N * v := by
  let K := 1 + halaszMertensConstant / Real.log 2
  let L := 1 + 2 * halaszMertensConstant / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨K * L, mul_pos hK hL, ?_⟩
  intro f hf N v hN hv P hP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := halasz_log_band_mass_linear hN0 hv P hP
  have hp (p : ℕ) (hp : p ∈ P) :
      ‖(Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))‖ ≤
        K * N * (Real.log (p : ℝ) / p) := by
    have hprime := (hP p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hy0 : 0 < (N : ℝ) / p := div_pos hN0 hp0
    have hy : (2 : ℝ) ≤ (N : ℝ) / p :=
      (Real.log_le_log_iff (by norm_num) hy0).mp (hv.trans (hP p hp).2.1)
    have hquot : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))]
    calc
      _ ≤ Real.log (p : ℝ) * 1 * (K * ((N : ℝ) / p)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf p hprime.pos) (by positivity))
          (halasz_prime_convolution_div_log f hf hy hquot) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [K]; ring
  calc
    _ ≤ ∑ p ∈ P, ‖(Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))‖ := norm_sum_le _ _
    _ ≤ K * N * ∑ p ∈ P, Real.log (p : ℝ) / p := by rw [mul_sum]; exact sum_le_sum hp
    _ ≤ K * N * (L * v) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszDoubleException
namespace OAI

/-! Sum the actual geometric prime bands. The central terms retain the
Halász saving, and both kinds of error have summable band weights. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical

theorem halasz_double_convolution_exception_oai : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ a b, 0 < a → 0 < b → f (a * b) = f a * f b) → OneBounded f →
    ∀ (N m : ℕ) (L T V W M₀ τ : ℝ), 2 ≤ N → 0 < m → m ≤ N →
      1 ≤ L → T ^ 2 ≤ L → B ≤ T → Real.log N ≤ V → 0 ≤ W → 0 ≤ M₀ →
      (∀ t ∈ Set.Ioc (-T) T, t ∉ Set.Ioc (τ-1/2) (τ+1/2) →
        ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ V * Real.exp (-M₀)) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszDoubleConvolution f N L‖ ≤
        C * N * (V+W) * (min M₀ (Real.log (1+|τ|)) + 1) *
          Real.exp (-min M₀ (Real.log (1+|τ|))) +
        C * N * W * Real.log N / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        C * m * Real.log (3 * N) ^ 2 := by
  obtain ⟨C₁, B, hC₁, hB, hanalytic⟩ := halasz_grouped_double_exception
  obtain ⟨C₂, hC₂, htrivial⟩ := halasz_grouped_double_trivial
  obtain ⟨G, hG, hgeometric⟩ := halasz_band_saving_sum
  let D := C₁ + C₂
  let C := 1 + D * G + 2 * D + 2 / Real.log 2
  have hD : 0 < D := add_pos hC₁ hC₂
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, B, hC, hB, ?_⟩
  intro f hf1 hf hbound N m L T V W M₀ τ hN hm hmN hL hTL hBT hNV hW hM₀ hFA hFW
  let P := mrtPrimeBand L ((N : ℝ) / 2)
  let J := halaszBandIndex (Real.log (N : ℝ)) + 1
  let M := min M₀ (Real.log (1+|τ|))
  let A₀ := V * Real.exp (-M₀)
  let A := (V+W) * Real.exp (-M)
  let δ := (m : ℝ) / ((N : ℝ) + 1 / 2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNlog : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlog0 : 0 < Real.log (N : ℝ) := htwo.trans_le hNlog
  have hV : 0 ≤ V := hlog0.le.trans hNV
  have hM : 0 ≤ M := le_min hM₀ (Real.log_nonneg (by linarith [abs_nonneg τ]))
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have heffective : A₀+W/(1+|τ|) ≤ A := by
    have h1 : Real.exp (-M₀) ≤ Real.exp (-M) :=
      Real.exp_le_exp.mpr (neg_le_neg (min_le_left _ _))
    have h2 : 1/(1+|τ|) ≤ Real.exp (-M) := by
      have hh := Real.exp_le_exp.mpr (neg_le_neg (min_le_right M₀ (Real.log (1+|τ|))))
      rw [Real.exp_neg,Real.exp_log (by positivity : 0 < 1+|τ|)] at hh
      simpa only [one_div,M] using hh
    dsimp [A₀,A]
    have hv := mul_le_mul_of_nonneg_left h1 hV
    have hw := mul_le_mul_of_nonneg_left h2 hW
    calc
      _ ≤ V*Real.exp (-M)+W*Real.exp (-M) :=
        add_le_add hv (by simpa only [mul_one_div] using hw)
      _ = _ := by ring
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < B) hBT
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC₁D : C₁ ≤ D := by dsimp [D]; linarith
  have hC₂D : C₂ ≤ D := by dsimp [D]; linarith
  have hPl (p : ℕ) (hp : p ∈ P) : p.Prime := mrtPrimeBand_prime hp
  have hpbounds (p : ℕ) (hp : p ∈ P) : Real.log 2 ≤ Real.log ((N : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) ≤ Real.log (N : ℝ) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPl p hp).pos
    have hb := mrtPrimeBand_bounds (show 0 ≤ L by linarith) (by positivity) hp
    have hquot : (2 : ℝ) ≤ (N : ℝ) / p := (le_div_iff₀ hp0).mpr (by linarith)
    exact ⟨Real.log_le_log (by norm_num) hquot,
      Real.log_le_log (div_pos hN0 hp0) (div_le_self hN0.le (by exact_mod_cast (hPl p hp).one_le))⟩
  have hpart : halaszDoubleConvolution f N L =
      ∑ j ∈ range J, halaszGroupedDouble f N (halaszPrimeBandPart P N j) := by
    exact halasz_prime_band_partition P (fun p hp => (hpbounds p hp).2) _
  have hpiece (j : ℕ) : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
      D * N * min A (halaszBandScale j) +
      D * N * halaszBandScale j * W / (δ * T) +
      (m : ℝ) / halaszBandScale j * Real.log (3 * N) ^ 2 := by
    let v := halaszBandScale j
    have hv : Real.log 2 ≤ v := halasz_band_scale_ge_log_two j
    have hv0 : 0 < v := htwo.trans_le hv
    have hPb : ∀ p ∈ halaszPrimeBandPart P N j, p.Prime ∧
        v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v := by
      intro p hp
      exact ⟨hPl p (mem_filter.mp hp).1,
        halasz_prime_band_part_bounds P (fun p hp => (hpbounds p hp).1) hp⟩
    have hPbig : ∀ p ∈ halaszPrimeBandPart P N j, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
        v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v := by
      intro p hp
      have hpp := (mem_filter.mp hp).1
      have hb := mrtPrimeBand_bounds (show 0 ≤ L by linarith) (by positivity) hpp
      exact ⟨(hPb p hp).1, hTL.trans hb.1.le, (hPb p hp).2⟩
    have ht := htrivial f hbound N v (by omega) hv _ hPb
    have ha := hanalytic f hf1 hf hbound N m v T A₀ W τ hN hm hmN hv hBT hA₀ hW _ hPbig hFA hFW
    have htD : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤ D * N * v :=
      ht.trans (by gcongr)
    have haD : ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
        D * N * A + D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2 :=
      ha.trans (by gcongr)
    change ‖halaszGroupedDouble f N (halaszPrimeBandPart P N j)‖ ≤
      D * N * min A v + D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2
    by_cases hvA : v ≤ A
    · rw [min_eq_right hvA]
      have herr : 0 ≤ D * N * v * W / (δ * T) + (m : ℝ) / v * Real.log (3 * N) ^ 2 := by positivity
      linarith
    · rw [min_eq_left (le_of_not_ge hvA)]
      exact haD
  have htop : halaszBandScale J ≤ 2 * Real.log (N : ℝ) := by
    have hb := (halasz_band_scale_bounds hNlog).1
    have he : halaszBandScale J = 2 * halaszBandScale (halaszBandIndex (Real.log (N : ℝ))) := by
      dsimp [J, halaszBandScale]
      rw [pow_succ]
      ring
    rw [he]
    linarith
  have hmin := hgeometric J (V+W) M (add_nonneg hV hW) hM (htop.trans (by linarith))
  have hscales := (halasz_band_scale_sum_le J).trans htop
  have hinverses := halasz_band_inverse_sum_le J
  have hsum : ‖halaszDoubleConvolution f N L‖ ≤
      (D * N) * (∑ j ∈ range J, min A (halaszBandScale j)) +
      (D * N * W / (δ * T)) * (∑ j ∈ range J, halaszBandScale j) +
      ((m : ℝ) * Real.log (3 * N) ^ 2) * (∑ j ∈ range J, (halaszBandScale j)⁻¹) := by
    rw [hpart]
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun j _ => hpiece j)).trans_eq
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  have hc1 : D * G ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 2 / Real.log 2 by positivity]
  have hc2 : 2 * D ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ D * G by positivity, show 0 ≤ 2 / Real.log 2 by positivity]
  have hc3 : 2 / Real.log 2 ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ D * G by positivity]
  calc
    _ ≤ _ := hsum
    _ ≤ (D * N) * (G * (V+W) * (M + 1) * Real.exp (-M)) +
        (D * N * W / (δ * T)) * (2 * Real.log (N : ℝ)) +
        ((m : ℝ) * Real.log (3 * N) ^ 2) * (2 / Real.log 2) := by
      gcongr
    _ = (D * G) * N * (V+W) * (M + 1) * Real.exp (-M) +
        (2 * D) * N * W * Real.log N / (δ * T) +
        (2 / Real.log 2) * m * Real.log (3 * N) ^ 2 := by ring
    _ ≤ _ := by gcongr

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_double_convolution_exception_oai := @OAI.TwoPointCorrelations.halasz_double_convolution_exception_oai
