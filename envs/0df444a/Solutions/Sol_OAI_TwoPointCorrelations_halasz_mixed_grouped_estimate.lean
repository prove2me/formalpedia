-- Prove2me | solution 1 for OAI.TwoPointCorrelations.halasz_mixed_grouped_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:30:19.537989+00:00
-- url     : https://prove2.me/submissions/30d6cd8b-ffb1-491e-8473-84bc8a161aa5

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_bounded_prime_triple_estimate

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothSeries
namespace OAI

/-! The smooth Euler series used in the triple-convolution Perron formula.
The finite prime factors and the smooth factor are absolutely convergent
on the line Re(s)=1. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex _root_.MeasureTheory
open _root_.Erdos970 hiding B1 Bf Cf ChebyshevPsi DRinD1 DeltaSpike DeltaSpikeContinuous Err H_auxiliary I If_ext If_taxicab I₁ I₂ I₃ I₃₇ I₄ I₅ I₆ I₇ I₈ I₉ LogDerivZetaHasBound LogDerivZetaIsHoloSmall MellinConvolution MellinInverseTransform MellinTransform S_horiz S_max S_vert Smooth1 SmoothedChebyshev SmoothedChebyshevIntegrand ZetaZerosNearPoint aestronglyMeasurable_B1 ballDR e f_M lemKRinK1 lemKinDR lem_Contra_finiteKR lem_DRcompact lem_ballDR lem_bolzano_weierstrass lem_identity_infiniteKR lem_identity_theorem lem_identity_theoremKR lem_identity_theoremR lem_zeros_have_limit_point logDerivZeta riemannZeta0 sigma1Of zeroZ zerosetKfR zerosetKfRc zetaPartialSum
open scoped _root_.Classical _root_.LSeries.notation






lemma halasz_smooth_function_eq {f : ℕ → ℂ} {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    halaszSmoothFunction f N n = f n := by
  exact if_pos (Nat.mem_smoothNumbers_of_lt hn (Nat.lt_succ_of_le hnN))





end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Fourier.ModFivePsiDecay
namespace OAI

/-! Removal of the nonintegral-cutoff condition.  The Mangoldt sums only
depend on the floor; the midpoint of the same unit interval is always an
admissible triangular cutoff. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma modFive_half_cutoff_nonnat (N : ℕ) :
    ∀ n : ℕ, (N : ℝ) + 1 / 2 ≠ (n : ℝ) := by
  intro n he
  have hh : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
  have hn : 2 * N + 1 = 2 * n := by exact_mod_cast hh
  omega

lemma modFive_half_cutoff_floor (N : ℕ) :
    ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor <;> linarith



end TwoPointCorrelations

end OAI

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszTriplePrefix
namespace OAI

/-! Identify a grouped piece of the adaptive double convolution with the
actual coefficients to which narrow Perron inversion is applied. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.LSeries.notation

lemma halasz_convolution_prefix (a b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (a ⍟ b) n) =
      ∑ p ∈ Icc 1 N, a p * ∑ m ∈ Icc 1 (N / p), b m := by
  simp_rw [LSeries.convolution_def]
  rw [halasz_sum_divisorsAntidiagonal (fun p m => a p * b m) N,
    halasz_hyperbola_rows (fun p m => a p * b m) N]
  exact sum_congr rfl (fun p _ => (mul_sum _ _ _).symm)

lemma halasz_finite_convolution_prefix (P : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ)
    (hP : P ⊆ Icc 1 N) :
    (∑ n ∈ Icc 1 N, (halaszFiniteCoefficient P a ⍟ b) n) =
      ∑ p ∈ P, a p * ∑ m ∈ Icc 1 (N / p), b m := by
  rw [halasz_convolution_prefix]
  rw [← sum_subset hP (fun p _ hp => by simp [halaszFiniteCoefficient, hp])]
  apply sum_congr rfl
  intro p hp
  simp [halaszFiniteCoefficient, hp]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePolynomial
namespace OAI

/-! The finite prime factors in the Perron integrand, with the same
normalization as the prime mean-square theorem. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical






lemma halasz_prime_coefficient_square_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) {R : ℝ} (ha : ∀ p ∈ P, ‖a p‖ ≤ R) :
    (∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p)) ≤
      R ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha p hp) 2)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _))

lemma halasz_adaptive_coefficient_bound (f : ℕ → ℂ) (hf : OneBounded f)
    {X v : ℝ} (hv : 0 < v) {p : ℕ} (hp : 0 < p)
    (hlog : v ≤ Real.log (X / p)) :
    ‖f p / (Real.log (X / p) : ℂ)‖ ≤ v⁻¹ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hv.trans_le hlog)]
  exact (div_le_div_of_nonneg_right (hf p hp) (hv.le.trans hlog)).trans
    (by simpa only [one_div] using one_div_le_one_div_of_le hv hlog)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszBandWeights
namespace OAI

/-! On one logarithmic band the two prime mean-square masses cancel:
the adaptive denominator contributes v⁻² and the two prime masses O(v²). -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma halasz_prime_set_mass_le {Y : ℝ} (hY : 1 ≤ Y) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Y) :
    (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ Real.log Y + halaszMertensConstant := by
  have hsub : Q ⊆ sievePrimesUpTo Y := by
    intro q hq
    exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by linarith)).mpr (hQ q hq).2),
      (hQ q hq).1⟩
  exact (sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => Real.log (q : ℝ) / q)
    hsub (fun q hq _ => div_nonneg
      (Real.log_nonneg (by exact_mod_cast (sievePrimesUpTo_prime Y q hq).one_le))
      (Nat.cast_nonneg _))).trans (halasz_prime_prefix_mass_le hY)

theorem halasz_band_mean_square_weights : ∃ K : ℝ, 0 < K ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (X v : ℝ), 0 < X → Real.log 2 ≤ v →
    ∀ (P Q : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ v ≤ Real.log (X / p) ∧ Real.log (X / p) < 2 * v) →
      (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Real.exp (2 * v)) →
      Real.sqrt (∑ p ∈ P, ‖f p / (Real.log (X / p) : ℂ)‖ ^ 2 *
        (Real.log (p : ℝ) / p)) *
        Real.sqrt (∑ q ∈ Q, ‖f q‖ ^ 2 * (Real.log (q : ℝ) / q)) ≤ K := by
  let C₁ := 1 + 2 * halaszMertensConstant / Real.log 2
  let C₂ := 2 + halaszMertensConstant / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  refine ⟨Real.sqrt (C₁ * C₂), Real.sqrt_pos.mpr (mul_pos hC₁ hC₂), ?_⟩
  intro f hf X v hX hv P Q hP hQ
  have hv0 : 0 < v := htwo.trans_le hv
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hQl : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1
  have hpMass : (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ C₁ * v :=
    halasz_log_band_mass_linear hX hv P hP
  have hqMass : (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ C₂ * v := by
    have hm := halasz_prime_set_mass_le (Y := Real.exp (2 * v))
      (Real.one_le_exp_iff.mpr (by linarith)) Q hQ
    rw [Real.log_exp] at hm
    have hh := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ halaszMertensConstant / Real.log 2 from div_nonneg hM htwo.le)
    rw [div_mul_cancel₀ _ htwo.ne'] at hh
    dsimp [C₂]
    linarith
  let A := ∑ p ∈ P, ‖f p / (Real.log (X / p) : ℂ)‖ ^ 2 * (Real.log (p : ℝ) / p)
  let B := ∑ q ∈ Q, ‖f q‖ ^ 2 * (Real.log (q : ℝ) / q)
  have hA0 : 0 ≤ A := sum_nonneg (fun p hp => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _)))
  have hB0 : 0 ≤ B := sum_nonneg (fun q hq => mul_nonneg (sq_nonneg _)
    (div_nonneg (Real.log_nonneg (by exact_mod_cast (hQl q hq).one_le)) (Nat.cast_nonneg _)))
  have hA : A ≤ C₁ / v := by
    calc
      _ ≤ (v⁻¹) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) / p :=
        halasz_prime_coefficient_square_mass P _ hPl
          (fun p hp => halasz_adaptive_coefficient_bound f hf hv0 (hPl p hp).pos (hP p hp).2.1)
      _ ≤ (v⁻¹) ^ 2 * (C₁ * v) := mul_le_mul_of_nonneg_left hpMass (sq_nonneg _)
      _ = _ := by field_simp
  have hB : B ≤ C₂ * v := by
    have hb := halasz_prime_coefficient_square_mass Q f hQl (fun q hq => hf q (hQl q hq).pos)
    simpa only [one_pow, one_mul] using hb.trans (by simpa only [one_pow, one_mul] using hqMass)
  have hAB : A * B ≤ C₁ * C₂ := by
    calc
      _ ≤ (C₁ / v) * (C₂ * v) := mul_le_mul hA hB hB0 (by positivity)
      _ = _ := by field_simp
  have hs := Real.sqrt_le_sqrt hAB
  rw [Real.sqrt_mul hA0] at hs
  exact hs

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedTriplePrefix
namespace OAI

/-! The mixed double convolution is the finite prefix of the
prime-prime-typical smooth series used by Perron inversion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical _root_.LSeries.notation

lemma halasz_mixed_smooth_prefix (G B : ℕ → ℂ) (N M : ℕ) (hMN : M ≤ N)
    {R : ℝ} (hL : 0 ≤ R) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q : ℕ, q.Prime → q ≤ M → (q ∈ Q ↔ R < (q:ℝ))) :
    (∑ n ∈ Icc 1 M,
      (halaszFiniteCoefficient Q (fun q => (Real.log (q:ℝ):ℂ)*G q) ⍟
        halaszSmoothFunction B N) n) = halaszMixedPrimeConvolution G B M R M := by
  have hband : mrtPrimeBand R M = (Icc 1 M).filter (fun q => q∈Q) := by
    ext q
    constructor
    · intro hq
      have hp := mrtPrimeBand_prime hq
      have hb := mrtPrimeBand_bounds hL (Nat.cast_nonneg M) hq
      have hqM : q ≤ M := by exact_mod_cast hb.2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.pos,hqM⟩,(hcover q hp hqM).mpr hb.1⟩
    · intro hq
      obtain ⟨hqM,hqQ⟩ := mem_filter.mp hq
      have hp := hQ q hqQ
      have hlarge := (hcover q hp (mem_Icc.mp hqM).2).mp hqQ
      apply mem_sdiff.mpr
      constructor
      · apply mem_filter.mpr
        exact ⟨by simpa only [Nat.floor_natCast,mem_Iic] using (mem_Icc.mp hqM).2,hp⟩
      · intro hsmall
        have hh := sievePrimesUpTo_le R hL q hsmall
        linarith
  rw [halasz_convolution_prefix,halaszMixedPrimeConvolution,hband,sum_filter]
  apply sum_congr rfl
  intro q hq
  have hs : (∑ m ∈ Icc 1 (M/q), halaszSmoothFunction B N m) =
      ∑ m ∈ Icc 1 (M/q), B m := by
    apply sum_congr rfl
    intro m hm
    exact halasz_smooth_function_eq (mem_Icc.mp hm).1
      (((mem_Icc.mp hm).2.trans (Nat.div_le_self M q)).trans hMN)
  rw [hs]
  by_cases hqQ : q∈Q <;> simp [halaszFiniteCoefficient,hqQ,mul_assoc]

lemma halasz_mixed_grouped_triple_prefix (G B : ℕ → ℂ) (N : ℕ)
    {R : ℝ} (hL : 0 ≤ R) (P Q : Finset ℕ) (hP : P ⊆ Icc 1 N)
    (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ p ∈ P, ∀ q : ℕ, q.Prime → q ≤ N/p → (q∈Q ↔ R < (q:ℝ))) :
    (∑ n ∈ Icc 1 N,
      (halaszFiniteCoefficient P
        (fun p => (Real.log (p:ℝ):ℂ)*G p/(Real.log ((N:ℝ)/p):ℂ)) ⍟
        (halaszFiniteCoefficient Q (fun q => (Real.log (q:ℝ):ℂ)*G q) ⍟
          halaszSmoothFunction B N)) n) = halaszMixedGrouped G B N R P := by
  rw [halasz_finite_convolution_prefix P _ _ N hP]
  unfold halaszMixedGrouped
  apply sum_congr rfl
  intro p hp
  rw [halasz_mixed_smooth_prefix G B N (N/p) (Nat.div_le_self N p) hL Q hQ (hcover p hp)]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedGrouped
namespace OAI

/-! The Perron estimate for one mixed logarithmic prime block. Both prime
factors avoid the small deleted bands; the smooth coefficient retains
the literal typical mask. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Complex
open scoped _root_.Classical _root_.LSeries.notation

theorem halasz_mixed_grouped_estimate_oai : ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (G B : ℕ → ℂ), OneBounded G → OneBounded B →
    ∀ (N m : ℕ) (R v T A W : ℝ), 0 ≤ R → 2 ≤ N → 0 < m → m ≤ N → Real.log 2 ≤ v →
      T₀ ≤ T → 0 ≤ A → 0 ≤ W →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ) ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      (∀ t ∈ Set.Icc (-T) T, ‖LSeries (halaszSmoothFunction B N) (1 + (t : ℂ) * I)‖ ≤ A) →
      (∀ t : ℝ, ‖LSeries (halaszSmoothFunction B N) (1 + (t : ℂ) * I)‖ ≤ W) →
      ‖halaszMixedGrouped G B N R P‖ ≤ C * N * A +
        C * N * v * W / (((m : ℝ) / ((N : ℝ) + 1 / 2)) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
  obtain ⟨C₀, T₀, hC₀, hT₀, htriple⟩ := halasz_bounded_prime_triple_estimate
  obtain ⟨K, hK, hweights⟩ := halasz_band_mean_square_weights
  let U := 1 + 2 * halaszMertensConstant / Real.log 2
  let V := 2 + halaszMertensConstant / Real.log 2
  let C := 2 * C₀ * K + 80 * U * V
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro G B hG hB N m R v T A W hL hN hm hmN hv hBT hA hW P hP hFA hFW
  let x : ℝ := (N : ℝ) + 1 / 2
  let Q := mrtPrimeBand R (Real.exp (2 * v))
  let a := fun p : ℕ => G p / (Real.log ((N : ℝ) / p) : ℂ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxle : x ≤ 2 * N := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp [x]
    linarith
  have hv0 : 0 < v := htwo.trans_le hv
  have hT : 0 < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < T₀) hBT
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmle : (m : ℝ) ≤ x := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    dsimp [x]
    linarith
  have hPl : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hPb : ∀ p ∈ P, p.Prime ∧ v ≤ Real.log ((N : ℝ) / p) ∧
      Real.log ((N : ℝ) / p) < 2 * v := fun p hp => ⟨(hP p hp).1, (hP p hp).2.2⟩
  have hQl : ∀ q ∈ Q, q.Prime := fun _ hq => mrtPrimeBand_prime hq
  have hQb : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ Real.exp (2 * v) := fun q hq =>
    ⟨hQl q hq, (mrtPrimeBand_bounds hL (Real.exp_pos _).le hq).2⟩
  have hPsub : P ⊆ Icc 1 N := by
    intro p hp
    have he := (halasz_log_band_endpoints hN0 (hPl p hp) (hP p hp).2.2.1 (hP p hp).2.2.2).2
    have hdiv : (N : ℝ) / Real.exp v ≤ N :=
      div_le_self hN0.le (Real.one_le_exp_iff.mpr hv0.le)
    exact mem_Icc.mpr ⟨(hPl p hp).pos, by exact_mod_cast he.trans hdiv⟩
  have hcover : ∀ p ∈ P, ∀ q, q.Prime → q ≤ N / p → (q ∈ Q ↔ R < (q:ℝ)) := by
    intro p hp q hq hqN
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hPl p hp).pos
    have hcut : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    have hy0 : 0 < (N : ℝ) / p := div_pos hN0 hp0
    have hupper := (Real.log_lt_iff_lt_exp hy0).mp (hP p hp).2.2.2
    have hqr : (q : ℝ) ≤ Real.exp (2 * v) := (by exact_mod_cast hqN : (q : ℝ) ≤ ((N / p : ℕ) : ℝ)).trans
      (hcut.trans hupper.le)
    constructor
    · intro hmem
      exact (mrtPrimeBand_bounds hL (Real.exp_pos _).le hmem).1
    · intro hlarge
      apply mem_sdiff.mpr
      refine ⟨mem_filter.mpr ⟨mem_Iic.mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mpr hqr),hq⟩,?_⟩
      intro hsmall
      exact (not_le_of_gt hlarge) (sievePrimesUpTo_le R hL q hsmall)
  have ha : ∀ p ∈ P, ‖a p‖ ≤ v⁻¹ := fun p hp =>
    halasz_adaptive_coefficient_bound G hG hv0 (hPl p hp).pos (hP p hp).2.2.1
  have hb : ∀ q ∈ Q, ‖G q‖ ≤ 1 := fun q hq => hG q (hQl q hq).pos
  have hestimate := htriple B hB N x T A W (v⁻¹) m hx hm hmle
    (modFive_half_cutoff_nonnat N) hBT hA hW (inv_nonneg.mpr hv0.le) P Q
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) hQl a G ha hb hFA hFW
  have heqa : (fun p : ℕ => (Real.log (p : ℝ) : ℂ) * a p) =
      fun p : ℕ => (Real.log (p : ℝ) : ℂ) * G p / (Real.log ((N : ℝ) / p) : ℂ) := by
    funext p
    dsimp [a]
    ring
  rw [show ⌊x⌋₊ = N from modFive_half_cutoff_floor N, heqa,
    halasz_mixed_grouped_triple_prefix G B N hL P Q hPsub hQl hcover] at hestimate
  have hweight := hweights G hG N v hN0 hv P Q hPb hQb
  have hpMass : (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ U * v :=
    halasz_log_band_mass_linear hN0 hv P hPb
  have hqMass : (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ V * v := by
    have hq := halasz_prime_set_mass_le (Y := Real.exp (2 * v))
      (Real.one_le_exp_iff.mpr (by linarith)) Q hQb
    rw [Real.log_exp] at hq
    have hscale := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ halaszMertensConstant / Real.log 2 from div_nonneg hM htwo.le)
    rw [div_mul_cancel₀ _ htwo.ne'] at hscale
    dsimp [V]
    linarith
  have hp0 : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) / p := sum_nonneg (fun p hp =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hPl p hp).one_le)) (Nat.cast_nonneg _))
  have hq0 : 0 ≤ ∑ q ∈ Q, Real.log (q : ℝ) / q := sum_nonneg (fun q hq =>
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hQl q hq).one_le)) (Nat.cast_nonneg _))
  have hsmall : v⁻¹ * (∑ p ∈ P, Real.log (p : ℝ) / p) ≤ U := by
    apply (mul_le_mul_of_nonneg_left hpMass (inv_nonneg.mpr hv0.le)).trans_eq
    field_simp
  have hprod : (v⁻¹ * ∑ p ∈ P, Real.log (p : ℝ) / p) *
      (∑ q ∈ Q, Real.log (q : ℝ) / q) ≤ U * (V * v) :=
    mul_le_mul hsmall hqMass hq0 hU.le
  have hlog : Real.log (x + m) ^ 2 ≤ Real.log (3 * N) ^ 2 := by
    have hmr : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    apply pow_le_pow_left₀ (Real.log_nonneg (by dsimp [x]; linarith))
    exact Real.log_le_log (by positivity) (by dsimp [x]; linarith)
  have hcmain : 2 * C₀ * K ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 80 * U * V by positivity]
  have hctail : 80 * U * V ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ 2 * C₀ * K by positivity]
  change ‖halaszMixedGrouped G B N R P‖ ≤ _ at hestimate ⊢
  calc
    _ ≤ _ := hestimate
    _ ≤ (C₀ * (2 * N) * A) * K +
        40 * (2 * N) * (U * (V * v)) * W / ((m / x) * T) +
        v⁻¹ * Real.log (3 * N) ^ 2 * m := by
      apply add_le_add
      · apply add_le_add
        · calc
            _ ≤ (C₀ * x * A) * K := mul_le_mul_of_nonneg_left hweight (by positivity)
            _ ≤ _ := by gcongr
        · calc
            _ = (40 * x * W / ((m / x) * T)) *
                ((v⁻¹ * ∑ p ∈ P, Real.log (p : ℝ) / p) *
                  (∑ q ∈ Q, Real.log (q : ℝ) / q)) := by ring
            _ ≤ (40 * x * W / ((m / x) * T)) * (U * (V * v)) :=
              mul_le_mul_of_nonneg_left hprod (by positivity)
            _ ≤ (40 * (2 * N) * W / ((m / x) * T)) * (U * (V * v)) := by
              gcongr
            _ = _ := by ring
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hv0.le)) (Nat.cast_nonneg m)
    _ ≤ C * N * A + C * N * v * W / ((m / x) * T) +
        (m : ℝ) / v * Real.log (3 * N) ^ 2 := by
      have hfirst := mul_le_mul_of_nonneg_right hcmain (show 0 ≤ (N : ℝ) * A by positivity)
      have hlast := mul_le_mul_of_nonneg_right hctail
        (show 0 ≤ (N : ℝ) * v * W / ((m / x) * T) by positivity)
      ring_nf at hfirst hlast ⊢
      linarith

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.halasz_mixed_grouped_estimate_oai := @OAI.TwoPointCorrelations.halasz_mixed_grouped_estimate_oai
