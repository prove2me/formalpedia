-- Prove2me | solution 1 for OAI.TwoPointCorrelations.sieve_prime_additive_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:53:22.894587+00:00
-- url     : https://prove2.me/submissions/92b714fa-d981-452c-9f97-522aecd245d3

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_sieve_goldbach_pairs_finite

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SievePrimeSubsets
namespace OAI

/-! Products of prime subsets realize distinct terms of the finite sieve denominator. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.OAI.Problem337
open scoped _root_.Classical


lemma sieve_prime_subset_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (↑P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hprod
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => hP p (mem_powerset.mp hS hp)
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_powerset.mp hT hp)
  calc
    S = (∏ p ∈ S, p).primeFactors := (Nat.primeFactors_prod hSp).symm
    _ = (∏ p ∈ T, p).primeFactors := congrArg Nat.primeFactors hprod
    _ = T := Nat.primeFactors_prod hTp




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









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DivisibilityPrefix
namespace OAI

/-! Exact change of variables `x=u*z` for a divisibility indicator,
including the floor endpoint `floor(X/u)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma positivePrefix_eq_Icc (F : ℕ → ℂ) (X : ℕ) :
    positivePrefix F X = ∑ n ∈ Icc 1 X, F n := by
  simpa only [Nat.zero_add, positivePrefix] using (sum_Icc_shift F 0 X).symm

theorem divisibility_positivePrefix (F : ℕ → ℂ) (u X : ℕ) (hu : 0 < u) :
    positivePrefix (fun n => natDivisibilityIndicator u n * F n) X =
      positivePrefix (fun z => F (u * z)) (X / u) := by
  calc
    _ = ∑ n ∈ (Icc 1 X).filter (fun n => u ∣ n), F n := by
      rw [positivePrefix_eq_Icc, sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : u ∣ n <;> simp only [natDivisibilityIndicator, hn, ite_true, ite_false,
        one_mul, zero_mul]
    _ = ∑ z ∈ Icc 1 (X / u), F (u * z) := by
      symm
      apply sum_bij (fun z _ => u * z)
      · intro z hz
        obtain ⟨hz₁, hzX⟩ := mem_Icc.mp hz
        apply mem_filter.mpr
        refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hu hz₁, ?_⟩, dvd_mul_right u z⟩
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hu).mp hzX
      · intro z _ w _ heq
        exact Nat.eq_of_mul_eq_mul_left hu heq
      · intro n hn
        obtain ⟨hnI, hdiv⟩ := mem_filter.mp hn
        obtain ⟨hn₁, hnX⟩ := mem_Icc.mp hnI
        refine ⟨n / u, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, Nat.mul_div_cancel' hdiv⟩
        exact Nat.div_pos (Nat.le_of_dvd hn₁ hdiv) hu
      · intro z _
        rfl
    _ = _ := (positivePrefix_eq_Icc (fun z => F (u * z)) (X / u)).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRamareIdentity
namespace OAI

/-! The corrected Ramaré identity from MRT v3, equation (3.2).
The denominator retains `1_{p ∤ m}`; repeated prime factors are allowed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical











lemma mrt_count_multiples {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ m ∈ Icc 1 N, if p ∣ m then (1 : ℝ) else 0) = (N / p : ℕ) := by
  have he := divisibility_positivePrefix (fun _ => (1 : ℂ)) p N hp
  simp only [positivePrefix_eq_Icc, natDivisibilityIndicator, mul_one,
    sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, apply_ite, Complex.one_re, Complex.zero_re,
    Complex.natCast_re] using hr


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveDivisorAverage
namespace OAI

/-! Averaging a nonnegative divisor sum by counting its multiples. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sieve_divisors_filter {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors = (Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hdn, _⟩ := Nat.mem_divisors.mp hd
    exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hn hdn).trans hnN⟩, hdn⟩
  · intro hd
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hn.ne'⟩

theorem sieve_divisor_sum_average (N : ℕ) (a : ℕ → ℝ)
    (ha : ∀ d, 0 ≤ a d) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, a d) ≤
      (N : ℝ) * ∑ d ∈ Icc 1 N, a d / d := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, if d ∣ n then a d else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [sieve_divisors_filter (mem_Icc.mp hn).1 (mem_Icc.mp hn).2, sum_filter]
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ Icc 1 N, if d ∣ n then a d else 0 := sum_comm
    _ = ∑ d ∈ Icc 1 N, a d * ((N / d : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro d hd
      have hc := mrt_count_multiples (N := N) (mem_Icc.mp hd).1
      rw [show (∑ n ∈ Icc 1 N, if d ∣ n then a d else 0) =
          a d * (∑ n ∈ Icc 1 N, if d ∣ n then (1 : ℝ) else 0) by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        split_ifs <;> simp]
      rw [hc]
    _ ≤ ∑ d ∈ Icc 1 N, a d * ((N : ℝ) / d) := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (ha d)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring

lemma sieve_inverse_sqrt_div {d : ℕ} (hd : 0 < d) :
    (1 / Real.sqrt (d : ℝ)) / d = (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_div, Real.rpow_neg hdr.le, one_div, Real.sqrt_eq_rpow]
  congr 1
  calc
    (d : ℝ) ^ (1 / 2 : ℝ) * d = (d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = (d : ℝ) ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hdr]; norm_num

theorem sieve_inverse_sqrt_divisor_average (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)) ≤
      (N : ℝ) * (∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ))) := by
  apply (sieve_divisor_sum_average N (fun d => 1 / Real.sqrt (d : ℝ)) (by intro d; positivity)).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  calc
    _ = ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply sum_congr rfl
      intro d hd
      exact sieve_inverse_sqrt_div (mem_Icc.mp hd).1
    _ ≤ _ := (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).sum_le_tsum _
      (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveEulerLower
namespace OAI

/-! The required logarithmic Euler-product lower bound and singular factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma sieve_euler_base_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [sub_pos, div_lt_one (by positivity)]
  exact hpR

lemma sieve_euler_factor_pos {p : ℕ} (hp : p.Prime) : 0 < sieveEulerFactor p :=
  inv_pos.mpr (sieve_euler_base_pos hp)

lemma sieve_euler_factor_one_le {p : ℕ} (hp : p.Prime) : 1 ≤ sieveEulerFactor p := by
  unfold sieveEulerFactor
  apply (one_le_inv₀ (sieve_euler_base_pos hp)).mpr
  have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  linarith





lemma sieve_singular_factor_one_le (N : ℕ) : 1 ≤ sieveSingularFactor N := by
  apply Finset.one_le_prod
  intro p hp
  exact sieve_euler_factor_one_le (Nat.mem_primeFactors.mp hp).1



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveSingularLocal
namespace OAI

/-! An elementary square-root divisor majorant for the sieve singular factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sieve_euler_factor_eq {p : ℕ} (hp : p.Prime) :
    sieveEulerFactor p = (p : ℝ) / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold sieveEulerFactor
  field_simp

lemma sieve_euler_factor_le_two {p : ℕ} (hp : p.Prime) : sieveEulerFactor p ≤ 2 := by
  rw [sieve_euler_factor_eq hp]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
  linarith

lemma sieve_euler_square_le {p : ℕ} (hp : p.Prime) :
    sieveEulerFactor p ^ 2 ≤ 1 + 6 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  rw [sieve_euler_factor_eq hp, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hp1)).mpr
  apply (mul_le_mul_iff_right₀ hp0).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hpR) (show (0 : ℝ) ≤ 4 * p - 3 by linarith)]

lemma sieve_euler_square_sqrt {p : ℕ} (hp : p.Prime) (hp36 : 36 ≤ p) :
    sieveEulerFactor p ^ 2 ≤ 1 + 1 / Real.sqrt (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs2 := Real.sq_sqrt hp0.le
  have hs6 : (6 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    have : (36 : ℝ) ≤ p := by exact_mod_cast hp36
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  have he : 6 / (p : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by
    apply (div_le_div_iff₀ hp0 hs0).mpr
    nlinarith
  exact (sieve_euler_square_le hp).trans (by linarith)

lemma sieve_singular_square_product (N : ℕ) :
    sieveSingularFactor N ^ 2 ≤
      (4 : ℝ) ^ 36 * (∏ p ∈ N.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) := by
  let P := N.primeFactors
  let S := P.filter (fun p => p < 36)
  have hsmall : S.card ≤ 36 := by
    have hs : S ⊆ range 36 := by
      intro p hp
      exact mem_range.mpr (mem_filter.mp hp).2
    simpa using card_le_card hs
  have hfac (p : ℕ) (hp : p ∈ P) :
      sieveEulerFactor p ^ 2 ≤ (if p < 36 then 4 else 1) * (1 + 1 / Real.sqrt (p : ℝ)) := by
    have hprime := (Nat.mem_primeFactors.mp hp).1
    by_cases h36 : p < 36
    · rw [if_pos h36]
      have he := pow_le_pow_left₀ (sieve_euler_factor_pos hprime).le (sieve_euler_factor_le_two hprime) 2
      have : 0 ≤ 1 / Real.sqrt (p : ℝ) := by positivity
      nlinarith
    · rw [if_neg h36, one_mul]
      exact sieve_euler_square_sqrt hprime (by omega)
  have hp := Finset.prod_le_prod (fun p _ => sq_nonneg (sieveEulerFactor p)) hfac
  have hconst : (∏ p ∈ P, (if p < 36 then (4 : ℝ) else 1)) ≤ (4 : ℝ) ^ 36 := by
    have he : (∏ p ∈ P, (if p < 36 then (4 : ℝ) else 1)) = (4 : ℝ) ^ S.card := by
      rw [← prod_filter]
      simp only [S, prod_const]
    rw [he]
    exact pow_le_pow_right₀ (by norm_num) hsmall
  rw [prod_mul_distrib, prod_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right hconst
    (prod_nonneg (fun p _ => by positivity)))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveSingularAverage
namespace OAI

/-! An absolute mean-square bound for the Goldbach singular factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sieve_prime_sqrt_product (P : Finset ℕ) :
    (∏ p ∈ P, 1 / Real.sqrt (p : ℝ)) = 1 / Real.sqrt ((∏ p ∈ P, p : ℕ) : ℝ) := by
  simp only [one_div]
  rw [Nat.cast_prod, Real.sqrt_prod P (fun p _ => Nat.cast_nonneg p)]
  exact prod_inv_distrib _

lemma sieve_prime_divisor_subsum {N : ℕ} (hN : N ≠ 0) :
    (∏ p ∈ N.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) ≤
      ∑ d ∈ N.divisors, 1 / Real.sqrt (d : ℝ) := by
  let P := N.primeFactors
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hi := sieve_prime_subset_injective P hP
  have himg : P.powerset.image (fun T => ∏ p ∈ T, p) ⊆ N.divisors := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
    apply Nat.mem_divisors.mpr
    exact ⟨(Finset.prod_dvd_prod_of_subset T P (fun p => p) (mem_powerset.mp hT)).trans
      (Nat.prod_primeFactors_dvd N), hN⟩
  calc
    _ = ∑ T ∈ P.powerset, ∏ p ∈ T, 1 / Real.sqrt (p : ℝ) := prod_one_add P
    _ = ∑ T ∈ P.powerset, 1 / Real.sqrt ((∏ p ∈ T, p : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro T _
      exact sieve_prime_sqrt_product T
    _ = ∑ d ∈ P.powerset.image (fun T => ∏ p ∈ T, p), 1 / Real.sqrt (d : ℝ) :=
      (sum_image (f := fun d : ℕ => 1 / Real.sqrt (d : ℝ)) hi).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)

lemma sieve_singular_square_divisor {N : ℕ} (hN : N ≠ 0) :
    sieveSingularFactor N ^ 2 ≤
      (4 : ℝ) ^ 36 * (∑ d ∈ N.divisors, 1 / Real.sqrt (d : ℝ)) :=
  (sieve_singular_square_product N).trans
    (mul_le_mul_of_nonneg_left (sieve_prime_divisor_subsum hN) (by positivity))


lemma sieve_singular_mean_constant_nonneg : 0 ≤ sieveSingularMeanConstant := by
  unfold sieveSingularMeanConstant
  positivity

/-- An absolute mean square for the singular factor, with no distribution
hypothesis on primes or on the target integer. -/
theorem sieve_singular_square_average (N : ℕ) :
    (∑ n ∈ Icc 1 N, sieveSingularFactor n ^ 2) ≤ sieveSingularMeanConstant * N := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (4 : ℝ) ^ 36 * (∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)) := by
      apply sum_le_sum
      intro n hn
      exact sieve_singular_square_divisor (by have := (mem_Icc.mp hn).1; omega)
    _ = (4 : ℝ) ^ 36 * (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, 1 / Real.sqrt (d : ℝ)) :=
      (mul_sum _ _ _).symm
    _ ≤ (4 : ℝ) ^ 36 * ((N : ℝ) * (∑' d : ℕ, (d : ℝ) ^ (-(3 / 2 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (sieve_inverse_sqrt_divisor_average N) (by positivity)
    _ = _ := by unfold sieveSingularMeanConstant; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveCutoffScale
namespace OAI

/-! The integer power cutoff needed to absorb the finite sieve remainder. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma sieve_power_cutoff_log {x : ℝ} (hx : 1 ≤ x)
    (hlog : 16 * Real.log 2 ≤ Real.log x) (hlarge : 4 ≤ x ^ (1 / 8 : ℝ)) :
    let z := ⌊x ^ (1 / 8 : ℝ)⌋₊
    2 ≤ z ∧ (z : ℝ) ≤ x ^ (1 / 8 : ℝ) ∧
      Real.log x / 16 ≤ Real.log z ∧ Real.log z ≤ Real.log x := by
  let y := x ^ (1 / 8 : ℝ)
  let z := ⌊y⌋₊
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx0 _
  have hz2 : 2 ≤ z := (Nat.le_floor_iff hy0.le).mpr (by dsimp [y]; linarith)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hzy : (z : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyz : y / 2 ≤ (z : ℝ) := by
    have hf := Nat.lt_floor_add_one y
    change y < (z : ℝ) + 1 at hf
    dsimp [y] at *
    linarith
  have hlow := Real.log_le_log (div_pos hy0 (by norm_num)) hyz
  rw [Real.log_div hy0.ne' (by norm_num), show Real.log y = (1 / 8 : ℝ) * Real.log x from
    Real.log_rpow hx0 _] at hlow
  have hyx : y ≤ x := Real.rpow_le_self_of_one_le hx (by norm_num)
  exact ⟨hz2, hzy, by linarith, Real.log_le_log hz0 (hzy.trans hyx)⟩

lemma sieve_power_cutoff_error {x : ℝ} {z : ℕ} (hx : 1 ≤ x)
    (hlog : 1 ≤ Real.log x) (hz : (z : ℝ) ≤ x ^ (1 / 8 : ℝ))
    (hzlog : Real.log z ≤ Real.log x) (hzlog0 : 0 ≤ Real.log z)
    (hsmall : Real.log x ^ 6 ≤ (1 / 32 : ℝ) * x ^ (1 / 2 : ℝ)) :
    (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z ≤ x / Real.log x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hy0 : 0 ≤ x ^ (1 / 8 : ℝ) := (zero_le_one.trans hy1)
  have hz2 := pow_le_pow_left₀ (Nat.cast_nonneg z) hz 2
  have hlogs := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log z)
    (show 1 + Real.log z ≤ 2 * Real.log x by linarith) 4
  have h6 : Real.log x ^ 2 ≤ Real.log x ^ 6 := pow_le_pow_right₀ hlog (by norm_num)
  have hy2 : x ^ (1 / 8 : ℝ) ≤ (x ^ (1 / 8 : ℝ)) ^ 2 := by nlinarith
  have hterm : (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z ≤
      (x ^ (1 / 8 : ℝ)) ^ 2 * (16 * Real.log x ^ 4 + 2) := by
    have hp := mul_le_mul hz2 hlogs (by positivity) (by positivity)
    nlinarith
  have hpoly : (16 * Real.log x ^ 4 + 2) * Real.log x ^ 2 ≤ 18 * Real.log x ^ 6 := by
    nlinarith
  have hpow : (x ^ (1 / 8 : ℝ)) ^ 2 * x ^ (1 / 2 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hx0.le, ← Real.rpow_add hx0]
    norm_num
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < Real.log x))).mpr
  calc
    _ ≤ ((x ^ (1 / 8 : ℝ)) ^ 2 * (16 * Real.log x ^ 4 + 2)) * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right hterm (sq_nonneg _)
    _ = (x ^ (1 / 8 : ℝ)) ^ 2 * ((16 * Real.log x ^ 4 + 2) * Real.log x ^ 2) := by ring
    _ ≤ (x ^ (1 / 8 : ℝ)) ^ 2 * (18 * Real.log x ^ 6) :=
      mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
    _ ≤ (x ^ (1 / 8 : ℝ)) ^ 2 * (18 * ((1 / 32 : ℝ) * x ^ (1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall (by norm_num)) (sq_nonneg _)
    _ = (18 / 32 : ℝ) * x ^ (3 / 4 : ℝ) := by rw [← hpow]; ring
    _ ≤ x ^ (3 / 4 : ℝ) := by nlinarith [Real.rpow_nonneg hx0.le (3 / 4 : ℝ)]
    _ ≤ x := Real.rpow_le_self_of_one_le hx (by norm_num)

theorem sieve_power_cutoff_eventually (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ Real.log x ∧
      let z := ⌊x ^ (1 / 8 : ℝ)⌋₊
      2 ≤ z ∧ A ≤ Real.log z ∧ Real.log x ≤ 16 * Real.log z ∧
        (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * z ≤ x / Real.log x ^ 2 := by
  have hl := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (max (16 * A) (16 * Real.log 2))))
  have hy := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).eventually
    (eventually_ge_atTop (4 : ℝ))
  have hs := (isLittleO_log_rpow_rpow_atTop (6 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound (by norm_num : (0 : ℝ) < 1 / 32)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl, hy, hs] with x hx hl hy hs
  have hlog : 1 ≤ Real.log x := (le_max_left _ _).trans hl
  have hA : 16 * A ≤ Real.log x := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have h2 : 16 * Real.log 2 ≤ Real.log x := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  obtain ⟨hz, hzx, hlow, hhigh⟩ := sieve_power_cutoff_log hx h2 hy
  have hsmall : Real.log x ^ 6 ≤ (1 / 32 : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [show Real.log x ^ (6 : ℝ) = Real.log x ^ (6 : ℕ) from Real.rpow_natCast _ _] at hs
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ Real.log x ^ (6 : ℕ)),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) (1 / 2 : ℝ))] using hs
  refine ⟨hx, hlog, hz, by linarith, by linarith, ?_⟩
  exact sieve_power_cutoff_error hx hlog hzx hhigh
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ ⌊x ^ (1 / 8 : ℝ)⌋₊ by omega))) hsmall

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveUniformPairs
namespace OAI

/-! A uniform Goldbach bound for all even targets below one common scale. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.OAI.Problem337

lemma sieve_pair_scale_algebra {C x L l S n : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hL : 0 < L) (hl : 0 < l)
    (hS : 1 ≤ S) (_hn : 0 ≤ n) (hnx : n ≤ 4 * x) (hLl : L ≤ 16 * l) :
    C * n * S / l ^ 2 + x / L ^ 2 ≤ (1024 * C + 1) * x * S / L ^ 2 := by
  have hS0 : 0 ≤ S := by linarith
  have hLsq : L ^ 2 ≤ 256 * l ^ 2 := by nlinarith
  have hratio : 1 / l ^ 2 ≤ 256 / L ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hl) (sq_pos_of_pos hL)).mpr
    nlinarith
  have hnS : C * n * S ≤ 4 * C * x * S := by
    nlinarith [mul_le_mul_of_nonneg_right hnx (mul_nonneg hC hS0)]
  have hxS : x ≤ x * S := by nlinarith
  calc
    _ = (C * n * S) * (1 / l ^ 2) + x / L ^ 2 := by ring
    _ ≤ (4 * C * x * S) * (256 / L ^ 2) + (x * S) / L ^ 2 := by
      apply add_le_add
      · exact mul_le_mul hnS hratio (by positivity) (by positivity)
      · exact div_le_div_of_nonneg_right hxS (sq_nonneg _)
    _ = _ := by ring

theorem sieve_goldbach_pairs_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ 1 ≤ Real.log x ∧ ∀ N : ℕ, N ≠ 0 → 2 ∣ N → (N : ℝ) ≤ 4 * x →
        ((PrimePairSieve.primePairs N).card : ℝ) ≤
          C * x * sieveSingularFactor N / Real.log x ^ 2 := by
  obtain ⟨C, hC, hpairs⟩ := sieve_goldbach_pairs_finite
  refine ⟨1024 * C + 1, by positivity, ?_⟩
  filter_upwards [sieve_power_cutoff_eventually (8 * (halaszMertensConstant + Real.log 2))]
    with x hx
  obtain ⟨hx1, hxlog, hz2, hzscale, hzlog, hzerr⟩ := hx
  refine ⟨hx1, hxlog, ?_⟩
  intro N hN0 hN hNx
  let z := ⌊x ^ (1 / 8 : ℝ)⌋₊
  have hzlogpos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have he := hpairs N z hN hN0 hz2 hzscale
  have halg := sieve_pair_scale_algebra hC.le (by linarith : 0 ≤ x)
    (by linarith : 0 < Real.log x) hzlogpos (sieve_singular_factor_one_le N)
    (Nat.cast_nonneg N) hNx hzlog
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SievePrimeEnergy
namespace OAI

/-! Prime additive energy from the finite Goldbach sieve and the singular-factor mean square. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.OAI.Problem337
open scoped _root_.Classical _root_.Pointwise

lemma sieve_prime_pair_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    ((P ×ˢ P).filter (fun v => v.1 + v.2 = N)).card ≤ (PrimePairSieve.primePairs N).card := by
  apply card_le_card_of_injOn Prod.fst
  · rintro ⟨p, q⟩ hpq
    obtain ⟨hpq, hsum⟩ := mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    have hp2 := (hP p hp).two_le
    have hq2 := (hP q hq).two_le
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
      hP p hp, by convert (preTransparency := .instances) hP q hq using 1; omega⟩
  · rintro ⟨p, q⟩ hpq ⟨r, s⟩ hrs heq
    have hsum1 := (mem_filter.mp hpq).2
    have hsum2 := (mem_filter.mp hrs).2
    change p = r at heq
    apply Prod.ext heq
    omega

lemma sieve_prime_sum_even {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    {N : ℕ} (hN : N ∈ P + P) : 2 ∣ N := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_add.mp hN
  have hpodd := (hP p hp).1.odd_of_ne_two (hP p hp).2
  have hqodd := (hP q hq).1.odd_of_ne_two (hP q hq).2
  exact (hpodd.add_odd hqodd).two_dvd

/-- The number of zero-sum prime quadruples has the required four logarithms
uniformly for every finite prime set below twice the scale. -/
theorem sieve_prime_additive_energy_oai :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * x) →
      (Finset.addEnergy P P : ℝ) ≤ C * x ^ 3 / Real.log x ^ 4 := by
  obtain ⟨C, hC, hevent⟩ := sieve_goldbach_pairs_uniform
  refine ⟨4 * C ^ 2 * (sieveSingularMeanConstant + 1), by
    have := sieve_singular_mean_constant_nonneg
    positivity, ?_⟩
  filter_upwards [hevent] with x hx
  obtain ⟨hx1, hxlog, hpairs⟩ := hx
  intro P hP
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  let A := C * x / Real.log x ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsub : P + P ⊆ Icc 1 ⌊4 * x⌋₊ := by
    intro N hN
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_add.mp hN
    have hp2 := (hP p hp).1.two_le
    have hq2 := (hP q hq).1.two_le
    apply mem_Icc.mpr
    constructor
    · omega
    · apply (Nat.le_floor_iff (by positivity : 0 ≤ 4 * x)).mpr
      push_cast
      linarith [(hP p hp).2.2, (hP q hq).2.2]
  have hpair (N : ℕ) (hN : N ∈ P + P) :
      (((P ×ˢ P).filter (fun v => v.1 + v.2 = N)).card : ℝ) ≤ A * sieveSingularFactor N := by
    have hNI := mem_Icc.mp (hsub hN)
    have hNx : (N : ℝ) ≤ 4 * x :=
      (show (N : ℝ) ≤ ⌊4 * x⌋₊ by exact_mod_cast hNI.2).trans (Nat.floor_le (by positivity))
    calc
      _ ≤ ((PrimePairSieve.primePairs N).card : ℝ) := by
        exact_mod_cast sieve_prime_pair_card P (fun p hp => (hP p hp).1) N
      _ ≤ C * x * sieveSingularFactor N / Real.log x ^ 2 := hpairs N (by omega)
        (sieve_prime_sum_even (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) hN) hNx
      _ = _ := by dsimp [A]; ring
  have henergy : (Finset.addEnergy P P : ℝ) ≤
      A ^ 2 * (∑ N ∈ Icc 1 ⌊4 * x⌋₊, sieveSingularFactor N ^ 2) := by
    rw [Finset.addEnergy_eq_sum_sq', Nat.cast_sum]
    calc
      _ = ∑ N ∈ P + P, (((P ×ˢ P).filter (fun v => v.1 + v.2 = N)).card : ℝ) ^ 2 := by
        simp only [Nat.cast_pow]
      _ ≤ ∑ N ∈ P + P, (A * sieveSingularFactor N) ^ 2 := by
        apply sum_le_sum
        intro N hN
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hpair N hN) 2
      _ = A ^ 2 * (∑ N ∈ P + P, sieveSingularFactor N ^ 2) := by
        simp only [mul_pow, mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => sq_nonneg _)) (sq_nonneg _)
  have havg := sieve_singular_square_average ⌊4 * x⌋₊
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 4 * x)
  have hK := sieve_singular_mean_constant_nonneg
  calc
    _ ≤ A ^ 2 * (sieveSingularMeanConstant * ⌊4 * x⌋₊) :=
      henergy.trans (mul_le_mul_of_nonneg_left havg (sq_nonneg _))
    _ ≤ A ^ 2 * (sieveSingularMeanConstant * (4 * x)) := by
      gcongr
    _ ≤ A ^ 2 * ((sieveSingularMeanConstant + 1) * (4 * x)) := by
      gcongr
      linarith
    _ = _ := by dsimp [A]; ring

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.sieve_prime_additive_energy_oai := @OAI.TwoPointCorrelations.sieve_prime_additive_energy_oai
