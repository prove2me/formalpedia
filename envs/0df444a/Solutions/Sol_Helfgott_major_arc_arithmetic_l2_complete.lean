-- Prove2me | solution 1 for Helfgott.major_arc_arithmetic_l2_complete
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T04:21:42.460531+00:00
-- url     : https://prove2.me/submissions/e662b258-97f2-47d1-b95f-f28aba7748b7

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott.SingularAux

noncomputable def totientLocal (p : ℕ) : ℝ :=
  if Nat.Prime p then (2*(p:ℝ)-1)/((p:ℝ)*((p:ℝ)-1)^2) else 0

lemma totientLocal_nonneg (p : ℕ) : 0 ≤ totientLocal p := by
  unfold totientLocal
  split_ifs with hp
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hn : 0 ≤ 2*(p:ℝ)-1 := by linarith
    positivity
  · rfl

lemma totientLocal_le_inv_square (p : ℕ) : totientLocal p ≤ 12/(p:ℝ)^2 := by
  unfold totientLocal
  split_ifs with hp
  · have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hm0 : (0:ℝ) < (p:ℝ)-1 := by linarith
    have hden : 0 < (p:ℝ)*((p:ℝ)-1)^2 := by positivity
    apply (div_le_div_iff₀ hden (by positivity : (0:ℝ) < (p:ℝ)^2)).2
    have hh : (p:ℝ)*(2*(p:ℝ)-1) ≤ 12*((p:ℝ)-1)^2 := by
      nlinarith [sq_nonneg ((p:ℝ)-2)]
    nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hh)]
  · positivity

lemma totientLocal_summable : Summable totientLocal := by
  have hs : Summable (fun p : ℕ => 12/(p:ℝ)^2) := by
    simpa only [mul_one_div] using
      ((Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))).mul_left (12:ℝ))
  exact hs.of_nonneg_of_le totientLocal_nonneg totientLocal_le_inv_square

lemma totientLocal_telescoping {p : ℕ} (hp : 32 ≤ p) :
    totientLocal p ≤ 3/((p:ℝ)-1)-3/(p:ℝ) := by
  have hpR : (32:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := by linarith
  have hm0 : (0:ℝ) < (p:ℝ)-1 := by linarith
  have hc : totientLocal p ≤ 3/(p:ℝ)^2 := by
    unfold totientLocal
    split_ifs with hprime
    · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hh : (p:ℝ)*(2*(p:ℝ)-1) ≤ 3*((p:ℝ)-1)^2 := by
        nlinarith [mul_nonneg hp0.le (by linarith : (0:ℝ) ≤ (p:ℝ)-5)]
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hh)]
    · positivity
  calc
    totientLocal p ≤ 3/(p:ℝ)^2 := hc
    _ ≤ 3/((p:ℝ)*((p:ℝ)-1)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    _ = 3/((p:ℝ)-1)-3/(p:ℝ) := by field_simp; ring

lemma totientLocal_tail_sum (n : ℕ) :
    ∑ k ∈ range n, totientLocal (k+32) ≤ 3/31-3/((n:ℝ)+31) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have hlocal := totientLocal_telescoping (p:=n+32) (by omega)
    have he : (n:ℝ)+32-1 = (n:ℝ)+31 := by ring
    simp only [Nat.cast_add,Nat.cast_ofNat,he] at hlocal
    simp only [Nat.cast_succ]
    rw [show (n:ℝ)+1+31 = (n:ℝ)+32 by ring]
    linarith

lemma prod_one_add_times_one_sub_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, (1+f i))*(1-∑ i ∈ s, f i) ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 := hf a (mem_insert_self a s)
    have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hi := ih hs0
    have hP : 0 ≤ ∏ i ∈ s, (1+f i) := prod_nonneg (fun i hi => by linarith [hs0 i hi])
    have hS : 0 ≤ ∑ i ∈ s, f i := sum_nonneg hs0
    rw [prod_insert ha,sum_insert ha]
    have hh : (1+f a)*(1-(f a+∑ i ∈ s,f i)) ≤ 1-∑ i ∈ s,f i := by
      nlinarith [mul_nonneg ha0 hS, sq_nonneg (f a)]
    calc
      _ = (∏ i ∈ s, (1+f i))*((1+f a)*(1-(f a+∑ i ∈ s,f i))) := by ring
      _ ≤ (∏ i ∈ s, (1+f i))*(1-∑ i ∈ s,f i) := mul_le_mul_of_nonneg_left hh hP
      _ ≤ 1 := hi

lemma totientLocal_tail_prod (n : ℕ) :
    ∏ k ∈ range n, (1+totientLocal (k+32)) ≤ 31/28 := by
  have hS : (∑ k ∈ range n, totientLocal (k+32)) ≤ 3/31 := by
    have hh := totientLocal_tail_sum n
    have hr : (0:ℝ) ≤ 3/((n:ℝ)+31) := by positivity
    linarith
  have hP : 0 ≤ ∏ k ∈ range n, (1+totientLocal (k+32)) :=
    prod_nonneg (fun k _ => by linarith [totientLocal_nonneg (k+32)])
  have hh := prod_one_add_times_one_sub_sum_le (range n)
    (fun k => totientLocal (k+32)) (fun k _ => totientLocal_nonneg (k+32))
  nlinarith [mul_nonneg hP (sub_nonneg.mpr hS)]

lemma totientLocal_prefix_prod : ∏ p ∈ range 32, (1+totientLocal p) ≤ 22/5 := by
  norm_num [totientLocal,prod_range_succ]

lemma totientLocal_partial_prod_upper (Q : ℕ) :
    ∏ p ∈ range Q, (1+totientLocal p) ≤ 5 := by
  by_cases hQ : Q ≤ 32
  · have hh : (∏ p ∈ range Q, (1+totientLocal p)) ≤
      ∏ p ∈ range 32, (1+totientLocal p) := by
      apply prod_le_prod_of_subset_of_one_le (range_mono hQ)
      · intro p _; linarith [totientLocal_nonneg p]
      · intro p _ _; linarith [totientLocal_nonneg p]
    linarith [totientLocal_prefix_prod]
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 32 ≤ Q)
    rw [prod_range_add]
    have hpre0 : 0 ≤ ∏ p ∈ range 32, (1+totientLocal p) :=
      prod_nonneg (fun p _ => by linarith [totientLocal_nonneg p])
    have htail0 : 0 ≤ ∏ k ∈ range n, (1+totientLocal (32+k)) :=
      prod_nonneg (fun k _ => by linarith [totientLocal_nonneg (32+k)])
    have htail : (∏ k ∈ range n, (1+totientLocal (32+k))) ≤ 31/28 := by
      simpa only [Nat.add_comm] using totientLocal_tail_prod n
    have hh := mul_le_mul totientLocal_prefix_prod htail htail0 (by norm_num : (0:ℝ) ≤ 22/5)
    norm_num at hh ⊢
    linarith

lemma totientLocal_multipliable : Multipliable (fun p : ℕ => 1+totientLocal p) := by
  apply multipliable_one_add_of_summable
  simpa only [Real.norm_eq_abs, abs_of_nonneg (totientLocal_nonneg _)] using totientLocal_summable

lemma totientLocal_euler_upper : (∏' p : ℕ, (1+totientLocal p)) ≤ 5 := by
  apply le_of_tendsto totientLocal_multipliable.tendsto_prod_tprod_nat
  exact Filter.Eventually.of_forall totientLocal_partial_prod_upper

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott.SingularAux

noncomputable def totientWeight (n : ℕ) : ℝ :=
  if Squarefree n then ∏ p ∈ n.primeFactors, totientLocal p else 0

lemma totientWeight_nonneg (n : ℕ) : 0 ≤ totientWeight n := by
  unfold totientWeight
  split_ifs
  · exact prod_nonneg (fun p _ => totientLocal_nonneg p)
  · rfl

lemma totientWeight_zero : totientWeight 0 = 0 := by simp [totientWeight]
lemma totientWeight_one : totientWeight 1 = 1 := by simp [totientWeight]

lemma totientWeight_mul {m n : ℕ} (h : Nat.Coprime m n) :
    totientWeight (m*n) = totientWeight m*totientWeight n := by
  classical
  by_cases hm : m = 0
  · simp [hm,totientWeight_zero]
  by_cases hn : n = 0
  · simp [hn,totientWeight_zero]
  unfold totientWeight
  simp only [Nat.squarefree_mul h,Nat.primeFactors_mul hm hn]
  by_cases hms : Squarefree m <;> by_cases hns : Squarefree n
  · simp only [hms,hns,and_self,if_true]
    exact prod_union h.disjoint_primeFactors
  · simp [hms,hns]
  · simp [hms,hns]
  · simp [hms,hns]

lemma totientWeight_summable : Summable totientWeight := by
  classical
  have hb : Summable (fun p : ℕ => ‖totientLocal p‖) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (totientLocal_nonneg _)] using totientLocal_summable
  have hs := summable_finsetProd_of_summable_norm hb
  have hi : Function.Injective (fun n : {n : ℕ | Squarefree n} => n.val.primeFactors) := by
    intro m n h
    change m.val.primeFactors = n.val.primeFactors at h
    apply Subtype.ext
    rw [← Nat.prod_primeFactors_of_squarefree m.prop,← Nat.prod_primeFactors_of_squarefree n.prop,h]
  have hh : Summable (fun n : {n : ℕ | Squarefree n} => totientWeight n.val) := by
    exact (hs.comp_injective hi).congr (fun n => by
      change (∏ p ∈ n.val.primeFactors,totientLocal p) = totientWeight n.val
      rw [totientWeight,if_pos (show Squarefree n.val from n.prop)])
  have hind := (summable_subtype_iff_indicator (s:={n : ℕ | Squarefree n}) (f:=totientWeight)).mp hh
  have he : Set.indicator {n : ℕ | Squarefree n} totientWeight = totientWeight := by
    funext n
    by_cases hn : Squarefree n <;> simp [totientWeight,hn]
  rwa [he] at hind

lemma totientWeight_prime {p : ℕ} (hp : Nat.Prime p) : totientWeight p = totientLocal p := by
  simp [totientWeight,hp.squarefree,hp.primeFactors]

lemma totientWeight_prime_pow_zero {p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k) :
    totientWeight (p^k) = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  simp [totientWeight,Nat.squarefree_pow_iff hp.ne_one hk0,hk1]

lemma totientWeight_prime_pow_tsum {p : ℕ} (hp : Nat.Prime p) :
    (∑' k : ℕ, totientWeight (p^k)) = 1+totientLocal p := by
  have hz : ∀ k ∉ range 2, totientWeight (p^k) = 0 := by
    intro k hk
    exact totientWeight_prime_pow_zero hp (by simpa only [mem_range,not_lt] using hk)
  rw [tsum_eq_sum hz]
  simp [sum_range_succ,totientWeight_one,totientWeight_prime hp]

lemma totientWeight_tsum_upper : (∑' n : ℕ, totientWeight n) ≤ 5 := by
  have hnorm : Summable (fun n : ℕ => ‖totientWeight n‖) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (totientWeight_nonneg _)] using totientWeight_summable
  have he := EulerProduct.eulerProduct_hasProd_mulIndicator totientWeight_one
    (fun {m n} h => totientWeight_mul h) hnorm totientWeight_zero
  have hfactor : Set.mulIndicator {p : ℕ | Nat.Prime p}
      (fun p => ∑' k : ℕ, totientWeight (p^k)) = (fun p : ℕ => 1+totientLocal p) := by
    funext p
    by_cases hp : Nat.Prime p
    · simp only [Set.mulIndicator_of_mem (show p ∈ {p : ℕ | Nat.Prime p} from hp)]
      exact totientWeight_prime_pow_tsum hp
    · simp [Set.mulIndicator_of_notMem,hp,totientLocal]
  rw [hfactor] at he
  rw [← he.tprod_eq]
  exact totientLocal_euler_upper

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology ArithmeticFunction.zeta
open Finset Filter

namespace Helfgott.SingularAux

noncomputable def totientDivisor : ArithmeticFunction ℝ :=
  ⟨fun n => (n:ℝ)*totientWeight n, by simp [totientWeight_zero]⟩

lemma totientDivisor_apply (n : ℕ) : totientDivisor n = (n:ℝ)*totientWeight n := rfl

lemma totientDivisor_multiplicative : totientDivisor.IsMultiplicative := by
  constructor
  · simp [totientDivisor_apply,totientWeight_one]
  · intro m n h
    simp only [totientDivisor_apply,Nat.cast_mul,totientWeight_mul h]
    ring

lemma totientDivisor_prime_pow_zero {p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k) :
    totientDivisor (p^k) = 0 := by
  simp [totientDivisor_apply,totientWeight_prime_pow_zero hp hk]

lemma totientDivisor_prime_pow_sum {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    ∑ i ∈ range (k+1), totientDivisor (p^i) = 1+(p:ℝ)*totientLocal p := by
  have he : (∑ i ∈ range 2, totientDivisor (p^i)) =
      ∑ i ∈ range (k+1), totientDivisor (p^i) := by
    apply sum_subset (range_mono (by omega : 2 ≤ k+1))
    intro i _ hi
    exact totientDivisor_prime_pow_zero hp (by simpa only [mem_range,not_lt] using hi)
  rw [← he]
  simp [sum_range_succ,totientDivisor_apply,totientWeight_one,totientWeight_prime hp]

lemma totientDivisor_convolution :
    (ζ : ArithmeticFunction ℝ)*totientDivisor =
      ArithmeticFunction.prodPrimeFactors (fun p => 1+(p:ℝ)*totientLocal p) := by
  have hz : (ζ : ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have hc := hz.mul totientDivisor_multiplicative
  have hH := ArithmeticFunction.IsMultiplicative.prodPrimeFactors (fun p => 1+(p:ℝ)*totientLocal p)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hc _ hH).2
  intro p k hp
  by_cases hk : k = 0
  · simp [hk,hc.map_one,hH.map_one]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [ArithmeticFunction.coe_zeta_mul_apply,Nat.sum_divisors_prime_pow hp,
      totientDivisor_prime_pow_sum hp hkpos,
      ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
      Nat.primeFactors_prime_pow hk hp]
    simp

lemma totientLocal_factor_ratio {p : ℕ} (hp : Nat.Prime p) :
    1+(p:ℝ)*totientLocal p = 1/(1-1/(p:ℝ))^2 := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm0 : (p:ℝ)-1 ≠ 0 := by
    have hh : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  rw [totientLocal,if_pos hp]
  field_simp
  ring

lemma totient_ratio_prod (n : ℕ) (hn : n ≠ 0) :
    (n:ℝ)^2/(Nat.totient n:ℝ)^2 =
      ∏ p ∈ n.primeFactors, (1+(p:ℝ)*totientLocal p) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hφ : (Nat.totient n:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have he : (Nat.totient n:ℝ) = (n:ℝ)*∏ p ∈ n.primeFactors,(1-1/(p:ℝ)) := by
    have hh := congrArg ((↑):ℚ→ℝ) (Nat.totient_eq_mul_prod_factors n)
    simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,Rat.cast_one,Rat.cast_inv,one_div] using hh
  rw [prod_congr rfl (fun p hp => totientLocal_factor_ratio (Nat.prime_of_mem_primeFactors hp))]
  rw [prod_div_distrib,prod_const_one,prod_pow]
  rw [he]
  field_simp

lemma inverse_totient_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    1/(Nat.totient n:ℝ)^2 =
      ∑ d ∈ n.divisors, (d:ℝ)*totientWeight d/(n:ℝ)^2 := by
  have hconv := congrArg (fun f : ArithmeticFunction ℝ => f n) totientDivisor_convolution
  rw [ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.prodPrimeFactors_apply hn,← totient_ratio_prod n hn] at hconv
  rw [← sum_div]
  have hh : (∑ d ∈ n.divisors,(d:ℝ)*totientWeight d) = (n:ℝ)^2/(Nat.totient n:ℝ)^2 := hconv
  rw [hh]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott.SingularAux

lemma inverseSquare_tail_finite (K M : ℕ) (hK : 0 < K) :
    ∑ n ∈ range M, 1/((n+K+1:ℕ):ℝ)^2 ≤ 1/(K:ℝ)-1/((M+K:ℕ):ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ]
    have hKR : (0:ℝ) < K := by exact_mod_cast hK
    have ht : (0:ℝ) < ((M+K:ℕ):ℝ) := by exact_mod_cast (show 0 < M+K by omega)
    have he : 1/((M+K+1:ℕ):ℝ)^2 ≤
        1/((M+K:ℕ):ℝ)-1/((M+K+1:ℕ):ℝ) := by
      have hu : ((M+K+1:ℕ):ℝ) = ((M+K:ℕ):ℝ)+1 := by push_cast; ring
      rw [hu]
      calc
        1/(((M+K:ℕ):ℝ)+1)^2 ≤ 1/(((M+K:ℕ):ℝ)*(((M+K:ℕ):ℝ)+1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        _ = 1/((M+K:ℕ):ℝ)-1/(((M+K:ℕ):ℝ)+1) := by field_simp; ring
    have hidx : M+1+K = M+K+1 := by omega
    simp only [hidx]
    linarith

lemma inverseSquare_tail_after (K : ℕ) (hK : 0 < K) :
    (∑' n : ℕ,1/((n+K+1:ℕ):ℝ)^2) ≤ 1/(K:ℝ) := by
  have hs0 : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))
  have hs : Summable (fun n : ℕ => 1/((n+K+1:ℕ):ℝ)^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (f:=fun n : ℕ => 1/(n:ℝ)^2) (K+1)).mpr hs0
  apply le_of_tendsto hs.tendsto_sum_tsum_nat
  apply Filter.Eventually.of_forall
  intro M
  have hh := inverseSquare_tail_finite K M hK
  have hr : (0:ℝ) ≤ 1/((M+K:ℕ):ℝ) := by positivity
  linarith

lemma inverseSquare_tail_start (K : ℕ) (hK : 0 < K) :
    (∑' n : ℕ,1/((n+K:ℕ):ℝ)^2) ≤ 2/(K:ℝ) := by
  have hs0 : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))
  have hs := (summable_nat_add_iff (f:=fun n : ℕ => 1/(n:ℝ)^2) K).mpr hs0
  have hid := hs.sum_add_tsum_nat_add 1
  simp only [sum_range_one,zero_add] at hid
  have hKR : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hh : 1/(K:ℝ)^2 ≤ 1/(K:ℝ) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hafter : (∑' n : ℕ, 1/((n+1+K:ℕ):ℝ)^2) ≤ 1/(K:ℝ) := by
    simpa only [Nat.add_right_comm] using inverseSquare_tail_after K hK
  rw [show 2/(K:ℝ) = 1/(K:ℝ)+1/(K:ℝ) by ring]
  linarith

lemma inverseSquare_finite_subset (K : ℕ) (hK : 0 < K) (s : Finset ℕ)
    (hsK : ∀ k ∈ s, K ≤ k) :
    ∑ k ∈ s,1/(k:ℝ)^2 ≤ 2/(K:ℝ) := by
  let M := s.sup id+1
  have hsub : s ⊆ Ico K (K+M) := by
    intro k hk
    have hkmax : k ≤ s.sup id := le_sup (f:=id) hk
    exact mem_Ico.mpr ⟨hsK k hk,by dsimp [M];omega⟩
  calc
    _ ≤ ∑ k ∈ Ico K (K+M),1/(k:ℝ)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ = ∑ n ∈ range M,1/((n+K:ℕ):ℝ)^2 := by
      rw [sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    _ ≤ ∑' n : ℕ,1/((n+K:ℕ):ℝ)^2 := by
      have hs0 : Summable (fun n : ℕ => 1/(n:ℝ)^2) :=
        Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))
      exact Summable.sum_le_tsum (range M) (fun n _ => by positivity)
        ((summable_nat_add_iff (f:=fun n : ℕ => 1/(n:ℝ)^2) K).mpr hs0)
    _ ≤ 2/(K:ℝ) := inverseSquare_tail_start K hK

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott.SingularAux

noncomputable def totientTailPair (Q : ℕ) (a : ℕ×ℕ) : ℝ :=
  if Q ≤ a.1*a.2 then totientWeight a.1/((a.1:ℝ)*(a.2:ℝ)^2) else 0

lemma totientTailPair_nonneg (Q : ℕ) (a : ℕ×ℕ) : 0 ≤ totientTailPair Q a := by
  unfold totientTailPair
  split_ifs
  · exact div_nonneg (totientWeight_nonneg _) (by positivity)
  · rfl

lemma totientTailPair_le_product (Q : ℕ) (a : ℕ×ℕ) :
    totientTailPair Q a ≤ totientWeight a.1*(1/(a.2:ℝ)^2) := by
  by_cases hd : a.1 = 0
  · simp [totientTailPair,hd,totientWeight_zero]
  have hdR : (1:ℝ) ≤ a.1 := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have hw : totientWeight a.1/(a.1:ℝ) ≤ totientWeight a.1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < a.1)).2
    nlinarith [mul_nonneg (totientWeight_nonneg a.1) (sub_nonneg.mpr hdR)]
  unfold totientTailPair
  split_ifs
  · calc
      _ = (totientWeight a.1/(a.1:ℝ))*(1/(a.2:ℝ)^2) := by
        simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (by positivity)
  · exact mul_nonneg (totientWeight_nonneg a.1) (by positivity)

lemma totientTailPair_summable (Q : ℕ) : Summable (totientTailPair Q) := by
  have hs : Summable (fun k : ℕ => 1/(k:ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2:ℕ))
  have hprod := totientWeight_summable.mul_of_nonneg hs totientWeight_nonneg (fun _ => by positivity)
  exact hprod.of_nonneg_of_le (fun a => totientTailPair_nonneg Q a)
    (fun a => totientTailPair_le_product Q a)

lemma totientTailPair_inner_upper (Q d : ℕ) (hQ : 0 < Q) :
    (∑' k : ℕ,totientTailPair Q (d,k)) ≤ (2/(Q:ℝ))*totientWeight d := by
  classical
  by_cases hd : d = 0
  · simp [hd,totientTailPair,totientWeight_zero]
  have hdR : (0:ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  apply tsum_le_of_sum_le' (mul_nonneg (by positivity) (totientWeight_nonneg d))
  intro s
  let t := s.filter (fun k => Q ≤ d*k)
  have he : (∑ k ∈ s,totientTailPair Q (d,k)) =
      (totientWeight d/(d:ℝ))*(∑ k ∈ t,1/(k:ℝ)^2) := by
    rw [mul_sum]
    rw [sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases hk : Q ≤ d*k
    · simp only [totientTailPair,hk,if_true]
      simp only [div_eq_mul_inv,mul_inv_rev];ring
    · simp [totientTailPair,hk]
  rw [he]
  by_cases ht : t.Nonempty
  · let K := t.min' ht
    have hKt : K ∈ t := min'_mem t ht
    have hqK : Q ≤ d*K := (mem_filter.mp hKt).2
    have hK : 0 < K := by
      by_contra hk
      have hk0 : K = 0 := by omega
      rw [hk0,Nat.mul_zero] at hqK
      omega
    have hKR : (0:ℝ) < K := by exact_mod_cast hK
    have hqKR : (Q:ℝ) ≤ (d:ℝ)*(K:ℝ) := by exact_mod_cast hqK
    have hsum := inverseSquare_finite_subset K hK t (fun k hk => min'_le t k hk)
    calc
      _ ≤ (totientWeight d/(d:ℝ))*(2/(K:ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (totientWeight_nonneg d) hdR.le)
      _ = (2*totientWeight d)/((d:ℝ)*(K:ℝ)) := by field_simp
      _ ≤ (2*totientWeight d)/(Q:ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (totientWeight_nonneg d)) hQR hqKR
      _ = (2/(Q:ℝ))*totientWeight d := by ring
  · rw [not_nonempty_iff_eq_empty.mp ht]
    simp only [sum_empty,mul_zero]
    exact mul_nonneg (by positivity) (totientWeight_nonneg d)

lemma totientTailPair_tsum_upper (Q : ℕ) (hQ : 0 < Q) :
    (∑' a : ℕ×ℕ,totientTailPair Q a) ≤ 10/(Q:ℝ) := by
  have hs := totientTailPair_summable Q
  have hr : Summable (fun d : ℕ => (2/(Q:ℝ))*totientWeight d) :=
    totientWeight_summable.mul_left _
  calc
    _ = ∑' d : ℕ, ∑' k : ℕ,totientTailPair Q (d,k) := hs.tsum_prod
    _ ≤ ∑' d : ℕ,(2/(Q:ℝ))*totientWeight d :=
      hs.prod.tsum_le_tsum (fun d => totientTailPair_inner_upper Q d hQ) hr
    _ = (2/(Q:ℝ))*(∑' d : ℕ,totientWeight d) := totientWeight_summable.tsum_mul_left _
    _ ≤ (2/(Q:ℝ))*5 := mul_le_mul_of_nonneg_left totientWeight_tsum_upper (by positivity)
    _ = 10/(Q:ℝ) := by ring

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Finset Filter

/-! Extracted supporting totient argument from tabbott's accepted Prove2Me
submission 08d91641-cd4f-4a91-8494-bcbc8c8c8e2d. The unrelated Vinogradov
assembly in that submission is omitted. Original mathematics and proof retained. -/

namespace Helfgott.SingularAux

/-! ## §1.  An elementary lower bound for Euler's totient

We prove `2 n³ ≤ 27 φ(n)⁴`, i.e. `φ(n) ≫ n^{3/4}`, which is enough to make `∑ φ(q)^{-2}`
converge by comparison with the `p`-series of exponent `3/2`. -/

/-- `p³ ≤ (p−1)⁴` for `p ≥ 5`. -/
theorem cube_le_sub_one_pow_four {p : ℕ} (hp : 5 ≤ p) : p ^ 3 ≤ (p - 1) ^ 4 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : 4 ≤ q := by omega
  simp only [Nat.add_sub_cancel]
  have h1 : 64 * (q + 1) ^ 3 ≤ 125 * q ^ 3 := by
    have hle : 4 * (q + 1) ≤ 5 * q := by omega
    have := Nat.pow_le_pow_left hle 3
    calc 64 * (q + 1) ^ 3 = (4 * (q + 1)) ^ 3 := by ring
      _ ≤ (5 * q) ^ 3 := this
      _ = 125 * q ^ 3 := by ring
  have h2 : 125 * q ^ 3 ≤ 64 * q ^ 4 := by
    have hc : 125 ≤ 64 * q := by omega
    calc 125 * q ^ 3 ≤ (64 * q) * q ^ 3 := Nat.mul_le_mul_right _ hc
      _ = 64 * q ^ 4 := by ring
  linarith

/-- For `n` coprime to `6`, `n³ ≤ φ(n)⁴`. -/
theorem cube_le_totient_pow_four (n : ℕ) :
    ¬ 2 ∣ n → ¬ 3 ∣ n → n ^ 3 ≤ Nat.totient n ^ 4 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      intro h2 h3
      have hp2 : p ≠ 2 := by rintro rfl; exact h2 (dvd_pow_self 2 hk.ne')
      have hp3 : p ≠ 3 := by rintro rfl; exact h3 (dvd_pow_self 3 hk.ne')
      have hp4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      have hp5 : 5 ≤ p := by have := hp.two_le; omega
      rw [Nat.totient_prime_pow hp hk]
      have hcube : p ^ 3 ≤ (p - 1) ^ 4 := cube_le_sub_one_pow_four hp5
      have e1 : (p ^ k) ^ 3 = p ^ (3 * (k - 1)) * p ^ 3 := by
        rw [← pow_add, ← pow_mul]; congr 1; omega
      have e2 : (p ^ (k - 1) * (p - 1)) ^ 4 = p ^ (4 * (k - 1)) * (p - 1) ^ 4 := by
        rw [mul_pow, ← pow_mul, mul_comm (k - 1) 4]
      rw [e1, e2]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right hp.pos (by omega)) hcube
  | zero => intro h2 _; exact absurd (dvd_zero 2) h2
  | one => intro _ _; simp
  | coprime a b _ _ hab iha ihb =>
      intro h2 h3
      have h2a : ¬ 2 ∣ a := fun h => h2 (h.mul_right b)
      have h2b : ¬ 2 ∣ b := fun h => h2 (h.mul_left a)
      have h3a : ¬ 3 ∣ a := fun h => h3 (h.mul_right b)
      have h3b : ¬ 3 ∣ b := fun h => h3 (h.mul_left a)
      rw [Nat.totient_mul hab, mul_pow, mul_pow]
      exact Nat.mul_le_mul (iha h2a h3a) (ihb h2b h3b)

theorem two_pow_bound (a : ℕ) : 2 ^ (3 * a) ≤ 8 * Nat.totient (2 ^ a) ^ 4 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_two ha]
    have e : (2 ^ (a - 1) * (2 - 1)) ^ 4 = 2 ^ (4 * (a - 1)) := by
      norm_num
      rw [← pow_mul, mul_comm]
    rw [e, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem three_pow_bound (b : ℕ) : 16 * 3 ^ (3 * b) ≤ 27 * Nat.totient (3 ^ b) ^ 4 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · rw [Nat.totient_prime_pow Nat.prime_three hb]
    have e : (3 ^ (b - 1) * (3 - 1)) ^ 4 = 16 * 3 ^ (4 * (b - 1)) := by
      rw [mul_pow, ← pow_mul, mul_comm (b - 1) 4]
      norm_num
      ring
    rw [e]
    have h : (27 : ℕ) * (16 * 3 ^ (4 * (b - 1))) = 16 * 3 ^ (3 + 4 * (b - 1)) := by
      rw [pow_add]; ring
    rw [h]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **`φ(n)⁴ ≥ (2/27) n³`.**  The constant `27/2` is the exact defect of the primes `2` and `3`. -/
theorem two_mul_cube_le (n : ℕ) : 2 * n ^ 3 ≤ 27 * Nat.totient n ^ 4 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hsplit : 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  set a := n.factorization 2 with ha
  set n₁ := n / 2 ^ a with hn₁def
  have hn₁0 : n₁ ≠ 0 := (Nat.ordCompl_pos 2 hn).ne'
  have h2n₁ : ¬ 2 ∣ n₁ := Nat.not_dvd_ordCompl Nat.prime_two hn
  have hcop1 : Nat.Coprime (2 ^ a) n₁ := (Nat.coprime_ordCompl Nat.prime_two hn).pow_left a
  have hsplit2 : 3 ^ (n₁.factorization 3) * (n₁ / 3 ^ (n₁.factorization 3)) = n₁ :=
    Nat.ordProj_mul_ordCompl_eq_self n₁ 3
  set b := n₁.factorization 3 with hb
  set m := n₁ / 3 ^ b with hmdef
  have h3m : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three hn₁0
  have hcop2 : Nat.Coprime (3 ^ b) m := (Nat.coprime_ordCompl Nat.prime_three hn₁0).pow_left b
  have h2m : ¬ 2 ∣ m := fun h => h2n₁ (h.trans (Nat.ordCompl_dvd n₁ 3))
  have hφ : Nat.totient n
      = Nat.totient (2 ^ a) * (Nat.totient (3 ^ b) * Nat.totient m) := by
    rw [← hsplit, Nat.totient_mul hcop1, ← hsplit2, Nat.totient_mul hcop2]
  have e1 : n ^ 3 = 2 ^ (3 * a) * (3 ^ (3 * b) * m ^ 3) := by
    rw [← hsplit, ← hsplit2]; ring
  have key : 16 * n ^ 3 ≤ 216 * Nat.totient n ^ 4 := by
    calc 16 * n ^ 3 = 2 ^ (3 * a) * ((16 * 3 ^ (3 * b)) * m ^ 3) := by rw [e1]; ring
      _ ≤ (8 * Nat.totient (2 ^ a) ^ 4)
            * ((27 * Nat.totient (3 ^ b) ^ 4) * Nat.totient m ^ 4) :=
          Nat.mul_le_mul (two_pow_bound a)
            (Nat.mul_le_mul (three_pow_bound b) (cube_le_totient_pow_four m h2m h3m))
      _ = 216 * Nat.totient n ^ 4 := by rw [hφ]; ring
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 8 by norm_num)
  calc 8 * (2 * n ^ 3) = 16 * n ^ 3 := by ring
    _ ≤ 216 * Nat.totient n ^ 4 := key
    _ = 8 * (27 * Nat.totient n ^ 4) := by ring

/-- **`∑_q φ(q)^{-2}` converges.**  (This is the lemma left `OPEN` as
`ThreePrimes.summable_inv_totient_sq` in `M_three_primes.lean`.) -/
theorem summable_inv_totient_sq :
    Summable (fun q : ℕ => 1 / (Nat.totient q : ℝ) ^ 2) := by
  have hs : Summable (fun n : ℕ => 4 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) hs
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  · have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
    set t : ℝ := (q : ℝ) ^ ((3 : ℝ) / 2) with ht
    have ht0 : 0 < t := Real.rpow_pos_of_pos hq0 _
    have htsq : t ^ 2 = (q : ℝ) ^ 3 := by
      rw [ht, ← Real.rpow_natCast ((q : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]
      norm_num
    have hnat : 2 * (q : ℝ) ^ 3 ≤ 27 * (Nat.totient q : ℝ) ^ 4 := by
      exact_mod_cast two_mul_cube_le q
    have hsq : (t / 4) ^ 2 ≤ ((Nat.totient q : ℝ) ^ 2) ^ 2 := by
      have e : ((Nat.totient q : ℝ) ^ 2) ^ 2 = (Nat.totient q : ℝ) ^ 4 := by ring
      rw [e]
      have h1 : (t / 4) ^ 2 = (q : ℝ) ^ 3 / 16 := by rw [div_pow, htsq]; norm_num
      rw [h1]
      have hnn : (0 : ℝ) ≤ (Nat.totient q : ℝ) ^ 4 := by positivity
      linarith
    have h4 : t / 4 ≤ (Nat.totient q : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((Nat.totient q : ℝ) ^ 2 - t / 4), ht0.le]
    calc 1 / (Nat.totient q : ℝ) ^ 2 ≤ 1 / (t / 4) :=
          one_div_le_one_div_of_le (by positivity) h4
      _ = 4 * (1 / t) := by field_simp

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Finset Filter

namespace Helfgott.SingularAux

lemma inverse_totient_square_finite_tail (Q M : ℕ) (hQ : 0 < Q) :
    ∑ q ∈ Ico Q (Q+M),1/(Nat.totient q:ℝ)^2 ≤ 10/(Q:ℝ) := by
  classical
  let s := Ico Q (Q+M)
  let a := s.sigma (fun q => q.divisors)
  let f : (Σ _ : ℕ,ℕ) → ℕ×ℕ := fun x => (x.2,x.1/x.2)
  have hprod : ∀ x ∈ a, x.2*(x.1/x.2) = x.1 := by
    intro x hx
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2)
  have hinj : Set.InjOn f (↑a) := by
    intro x hx y hy hxy
    have hd : x.2 = y.2 := congrArg Prod.fst hxy
    have hk : x.1/x.2 = y.1/y.2 := congrArg Prod.snd hxy
    have hq : x.1 = y.1 := by
      rw [← hprod x hx,← hprod y hy]
      exact congrArg₂ Nat.mul hd hk
    exact Sigma.ext hq (by simpa using hd)
  have hterm : ∀ q ∈ s, ∀ d ∈ q.divisors,
      (d:ℝ)*totientWeight d/(q:ℝ)^2 = totientTailPair Q (f ⟨q,d⟩) := by
    intro q hq d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hq0 : q ≠ 0 := Nat.ne_zero_of_mem_divisors hd
    have hqp : d*(q/d) = q := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    have hQq : Q ≤ q := (mem_Ico.mp hq).1
    have hQr : Q ≤ d*(q/d) := by rwa [hqp]
    simp only [f,totientTailPair,hQr,if_true]
    have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd0
    have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq0
    have hqcast : (d:ℝ)*((q/d:ℕ):ℝ) = (q:ℝ) := by exact_mod_cast hqp
    have hkR : ((q/d:ℕ):ℝ) ≠ 0 := by
      intro hk
      rw [hk,mul_zero] at hqcast
      exact hqR hqcast.symm
    rw [← hqcast]
    field_simp
  have he : (∑ q ∈ s,1/(Nat.totient q:ℝ)^2) =
      ∑ x ∈ a,totientTailPair Q (f x) := by
    dsimp only [a]
    rw [sum_sigma]
    apply sum_congr rfl
    intro q hq
    rw [inverse_totient_square_divisor_expansion q (by have hh := (mem_Ico.mp hq).1;omega)]
    exact sum_congr rfl (fun d hd => hterm q hq d hd)
  calc
    _ = ∑ x ∈ a,totientTailPair Q (f x) := he
    _ = ∑ b ∈ a.image f,totientTailPair Q b := (sum_image hinj).symm
    _ ≤ ∑' b : ℕ×ℕ,totientTailPair Q b :=
      Summable.sum_le_tsum (a.image f) (fun b _ => totientTailPair_nonneg Q b)
        (totientTailPair_summable Q)
    _ ≤ 10/(Q:ℝ) := totientTailPair_tsum_upper Q hQ

theorem inverse_totient_square_tail (Q : ℕ) (hQ : 0 < Q) :
    (∑' k : ℕ,1/(Nat.totient (k+Q):ℝ)^2) ≤ 10/(Q:ℝ) := by
  have hs := (summable_nat_add_iff
    (f:=fun q : ℕ => 1/(Nat.totient q:ℝ)^2) Q).mpr summable_inv_totient_sq
  apply le_of_tendsto hs.tendsto_sum_tsum_nat
  apply Filter.Eventually.of_forall
  intro M
  have hh := inverse_totient_square_finite_tail Q M hQ
  rw [sum_Ico_eq_sum_range] at hh
  simpa only [Nat.add_sub_cancel_left,Nat.add_comm] using hh

end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Metric

namespace Helfgott

theorem circle_arc_integral (f : AddCircle (1:ℝ) → ℂ) (c ε : ℝ)
    (hε : ε ≤ (1/2:ℝ)) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      ∫ t in Ioo (c-ε) (c+ε),f (t : AddCircle (1:ℝ)) := by
  have hv : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T:=1)
  rw [← hv,← integral_indicator measurableSet_ball]
  rw [← AddCircle.integral_preimage (1:ℝ) (c-1/2)]
  have hcoe (t : ℝ) (ht : t ∈ Ioc (c-1/2) (c-1/2+1)) :
      ((t : AddCircle (1:ℝ)) ∈ ball (c : AddCircle (1:ℝ)) ε) ↔
        t ∈ Ioo (c-ε) (c+ε) := by
    have htlo := (mem_Ioc.mp ht).1
    have hthi := (mem_Ioc.mp ht).2
    have habs : |t-c| ≤ (1:ℝ)/2 := by apply abs_le.mpr;constructor <;>linarith
    have hn : ‖((t-c:ℝ) : AddCircle (1:ℝ))‖ = |t-c| :=
      (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num)).mpr (by simpa using habs)
    simp only [mem_ball,dist_eq_norm,← AddCircle.coe_sub,hn,mem_Ioo]
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have he : (∫ t in Ioc (c-1/2) (c-1/2+1),
      (ball (c : AddCircle (1:ℝ)) ε).indicator f (t : AddCircle (1:ℝ))) =
      ∫ t in Ioc (c-1/2) (c-1/2+1),
        (Ioo (c-ε) (c+ε)).indicator (fun t : ℝ => f (t : AddCircle (1:ℝ))) t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    by_cases hm : t ∈ Ioo (c-ε) (c+ε)
    · rw [Set.indicator_of_mem ((hcoe t ht).mpr hm),Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem (fun hc => hm ((hcoe t ht).mp hc)),Set.indicator_of_notMem hm]
  rw [he,setIntegral_indicator measurableSet_Ioo]
  have hs : Ioo (c-ε) (c+ε) ⊆ Ioc (c-1/2) (c-1/2+1) := by
    intro t ht
    rcases mem_Ioo.mp ht with ⟨hl,hr⟩
    exact mem_Ioc.mpr ⟨by linarith,by linarith⟩
  rw [inter_eq_right.mpr hs]

theorem circle_arc_integral_scaled (f : AddCircle (1:ℝ) → ℂ) (c ε x : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ (1/2:ℝ)) (hx : 0 < x) :
    (∫ α in ball (c : AddCircle (1:ℝ)) ε,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Icc (-(x*ε)) (x*ε),f ((c+β/x : ℝ) : AddCircle (1:ℝ))) := by
  calc
    _ = ∫ t in Ioo (c-ε) (c+ε),f (t : AddCircle (1:ℝ)) := circle_arc_integral f c ε hε
    _ = ∫ u in (-ε)..ε,f ((c+u : ℝ) : AddCircle (1:ℝ)) := by
      rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : c-ε ≤ c+ε)]
      simpa only [sub_eq_add_neg] using
        (intervalIntegral.integral_comp_add_left (f:=fun t : ℝ => f (t : AddCircle (1:ℝ)))
          (a:= -ε) (b:=ε) c).symm
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by nlinarith : -(x*ε) ≤ x*ε)]
      have hs := intervalIntegral.integral_comp_div
        (f:=fun u : ℝ => f ((c+u : ℝ) : AddCircle (1:ℝ)))
        (a:= -(x*ε)) (b:=x*ε) hx.ne'
      simp only [neg_div,mul_div_cancel_left₀ ε hx.ne'] at hs
      rw [hs,smul_smul,inv_mul_cancel₀ hx.ne',one_smul]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Metric

namespace Helfgott

lemma reduced_fraction_cross_eq {a q b d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d) (he : a*d = b*q) :
    a = b ∧ q = d := by
  have hqd : q ∣ d := haq.symm.dvd_of_dvd_mul_left (by rw [he];exact dvd_mul_left q b)
  have hdq : d ∣ q := hbd.symm.dvd_of_dvd_mul_left (by rw [← he];exact dvd_mul_left d a)
  have hqdEq : q = d := Nat.dvd_antisymm hqd hdq
  have hab : a = b := Nat.eq_of_mul_eq_mul_right hd (by simpa only [hqdEq] using he)
  exact ⟨hab,hqdEq⟩

lemma reduced_fraction_circle_separation {a q b d : ℕ} (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hne : (a,q) ≠ (b,d)) :
    1/((q:ℝ)*(d:ℝ)) ≤ dist ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ))
      ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  let δ : ℝ := (a:ℝ)/(q:ℝ)-(b:ℝ)/(d:ℝ)
  let k : ℤ := (a:ℤ)*(d:ℤ)-(b:ℤ)*(q:ℤ)-round δ*(q:ℤ)*(d:ℤ)
  have hδlo : -1 < δ := by
    have hba : (b:ℝ)/(d:ℝ) < 1 := (div_lt_one hdR).mpr (by exact_mod_cast hb)
    have haa : 0 ≤ (a:ℝ)/(q:ℝ) := by positivity
    dsimp [δ]
    linarith
  have hδhi : δ < 1 := by
    have haa : (a:ℝ)/(q:ℝ) < 1 := (div_lt_one hqR).mpr (by exact_mod_cast ha)
    have hba : 0 ≤ (b:ℝ)/(d:ℝ) := by positivity
    dsimp [δ]
    linarith
  have hk : (k:ℝ) = (q:ℝ)*(d:ℝ)*(δ-(round δ:ℝ)) := by
    dsimp [k,δ]
    push_cast
    field_simp
  have hk0 : k ≠ 0 := by
    intro hzero
    have hzR : (k:ℝ) = 0 := by exact_mod_cast hzero
    rw [hk] at hzR
    have hδ : δ = (round δ:ℝ) := by
      have hδ0 := (mul_eq_zero.mp hzR).resolve_left (by positivity)
      exact sub_eq_zero.mp hδ0
    have hroundlo : (-1:ℤ) < round δ := by exact_mod_cast (hδ.symm ▸ hδlo)
    have hroundhi : round δ < (1:ℤ) := by exact_mod_cast (hδ.symm ▸ hδhi)
    have hround : round δ = 0 := by omega
    have hcrossR : (a:ℝ)*(d:ℝ) = (b:ℝ)*(q:ℝ) := by
      rw [hround,Int.cast_zero] at hδ
      dsimp only [δ] at hδ
      have ht := (sub_eq_zero.mp hδ)
      exact (div_eq_div_iff hqR.ne' hdR.ne').mp ht
    have hcross : a*d = b*q := by exact_mod_cast hcrossR
    rcases reduced_fraction_cross_eq hq hd haq hbd hcross with ⟨hab,hqd⟩
    exact hne (Prod.ext hab hqd)
  have hkabs : 1 ≤ |(k:ℝ)| := by
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hkneg : (k:ℝ) < 0 := by exact_mod_cast hneg
      rw [abs_of_neg hkneg]
      have hh : k ≤ -1 := by omega
      have hhR : (k:ℝ) ≤ -1 := by exact_mod_cast hh
      linarith
    · have hkpos : (0:ℝ) < k := by exact_mod_cast hpos
      rw [abs_of_pos hkpos]
      exact_mod_cast (show (1:ℤ) ≤ k by omega)
  have hnorm : dist ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ))
      ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) = |δ-(round δ:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    simp only [inv_one,one_mul,mul_one]
    rfl
  rw [hnorm]
  apply (div_le_iff₀ (mul_pos hqR hdR)).mpr
  rw [hk,abs_mul,abs_of_pos (mul_pos hqR hdR)] at hkabs
  simpa only [mul_comm] using hkabs

theorem major_arc_balls_disjoint {a q b d r : ℕ} {x : ℝ}
    (hq : 0 < q) (hd : 0 < d) (ha : a < q) (hb : b < d)
    (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hqr : q ≤ 2*r) (hdr : d ≤ 2*r) (hx : 32*(r:ℝ)^2 < x)
    (hne : (a,q) ≠ (b,d)) :
    Disjoint (ball ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((q:ℝ)*x)))
      (ball ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((d:ℝ)*x))) := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqrR : (q:ℝ) ≤ 2*r := by exact_mod_cast hqr
  have hdrR : (d:ℝ) ≤ 2*r := by exact_mod_cast hdr
  have hsep := reduced_fraction_circle_separation hq hd ha hb haq hbd hne
  have hrad : 8*(r:ℝ)/((q:ℝ)*x)+8*(r:ℝ)/((d:ℝ)*x) < 1/((q:ℝ)*(d:ℝ)) := by
    apply (lt_div_iff₀ (mul_pos hqR hdR)).mpr
    have he : (8*(r:ℝ)/((q:ℝ)*x)+8*(r:ℝ)/((d:ℝ)*x))*((q:ℝ)*(d:ℝ)) =
        8*(r:ℝ)*((q:ℝ)+(d:ℝ))/x := by
      field_simp
      ring
    rw [he]
    apply (div_lt_one hxR).mpr
    have hsum : (q:ℝ)+(d:ℝ) ≤ 4*r := by linarith
    have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 8*(r:ℝ))
    nlinarith
  apply Set.disjoint_left.mpr
  intro α hαq hαd
  have hdcenter := dist_triangle ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) α
    ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ))
  have hqdist := mem_ball.mp hαq
  have hddist := mem_ball.mp hαd
  rw [dist_comm _ α] at hdcenter
  linarith

theorem actual_major_arc_rational_unique {a q b d r : ℕ} {x : ℝ}
    (α : AddCircle (1:ℝ)) (hq : 0 < q) (hd : 0 < d)
    (ha : a < q) (hb : b < d) (haq : Nat.Coprime a q) (hbd : Nat.Coprime b d)
    (hx : 32*(r:ℝ)^2 < x)
    (hαq : (Odd q ∧ q ≤ r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*q*x)) ∨
      (Even q ∧ q ≤ 2*r ∧ dist α ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) < 8*r/(q*x)))
    (hαd : (Odd d ∧ d ≤ r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) <
        8*r/(2*d*x)) ∨
      (Even d ∧ d ≤ 2*r ∧ dist α ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) < 8*r/(d*x))) :
    a = b ∧ q = d := by
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hqr : q ≤ 2*r := by rcases hαq with h | h <;> omega
  have hdr : d ≤ 2*r := by rcases hαd with h | h <;> omega
  have hqball : α ∈ ball ((a:ℝ)/(q:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((q:ℝ)*x)) := by
    apply mem_ball.mpr
    rcases hαq with h | h
    · apply h.2.2.trans_le
      have hden : (0:ℝ) < q*x := mul_pos hqR hxR
      have hnum : 0 ≤ 8*(r:ℝ) := by positivity
      apply div_le_div_of_nonneg_left hnum hden
      nlinarith
    · exact h.2.2
  have hdball : α ∈ ball ((b:ℝ)/(d:ℝ) : AddCircle (1:ℝ)) (8*(r:ℝ)/((d:ℝ)*x)) := by
    apply mem_ball.mpr
    rcases hαd with h | h
    · apply h.2.2.trans_le
      have hden : (0:ℝ) < d*x := mul_pos hdR hxR
      have hnum : 0 ≤ 8*(r:ℝ) := by positivity
      apply div_le_div_of_nonneg_left hnum hden
      nlinarith
    · exact h.2.2
  by_contra hh
  have hne : (a,q) ≠ (b,d) := by
    intro he
    exact hh ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  exact Set.disjoint_left.mp (major_arc_balls_disjoint hq hd ha hb haq hbd hqr hdr hx hne) hqball hdball

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
open MeasureTheory Set Metric Finset Function
open scoped BigOperators

namespace Helfgott

noncomputable def actualArcDenominators (r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 r).filter (fun q => Odd q) ∪
    (Finset.Icc 1 (2*r)).filter (fun q => Even q)

noncomputable def actualArcIndices (r : ℕ) : Finset (Σ _ : ℕ,ℕ) :=
  (actualArcDenominators r).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))

noncomputable def actualArcRadius (r q : ℕ) (x : ℝ) : ℝ :=
  if Odd q then 4*(r:ℝ)/((q:ℝ)*x) else 8*(r:ℝ)/((q:ℝ)*x)

lemma actualArcIndices_mem (r : ℕ) (i : Σ _ : ℕ,ℕ) :
    i ∈ actualArcIndices r ↔ 0 < i.1 ∧ i.2 < i.1 ∧ Nat.Coprime i.2 i.1 ∧
      ((Odd i.1 ∧ i.1 ≤ r) ∨ (Even i.1 ∧ i.1 ≤ 2*r)) := by
  classical
  simp only [actualArcIndices,actualArcDenominators,Finset.mem_sigma,Finset.mem_union,
    Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
  constructor
  · rintro ⟨h,ha,hcop⟩
    rcases h with ⟨⟨hpos,hqr⟩,ho⟩ | ⟨⟨hpos,hqr⟩,he⟩
    · exact ⟨hpos,ha,hcop,Or.inl ⟨ho,hqr⟩⟩
    · exact ⟨hpos,ha,hcop,Or.inr ⟨he,hqr⟩⟩
  · rintro ⟨hpos,ha,hcop,h⟩
    constructor
    · rcases h with ⟨ho,hqr⟩ | ⟨he,hqr⟩
      · exact Or.inl ⟨⟨hpos,hqr⟩,ho⟩
      · exact Or.inr ⟨⟨hpos,hqr⟩,he⟩
    · exact ⟨ha,hcop⟩

lemma actualArcRadius_odd (r q : ℕ) (x : ℝ) (ho : Odd q) :
    actualArcRadius r q x = 8*r/(2*q*x) := by
  rw [actualArcRadius,if_pos ho]
  ring_nf

lemma actualArcRadius_even (r q : ℕ) (x : ℝ) (he : Even q) :
    actualArcRadius r q x = 8*r/(q*x) := by
  rw [actualArcRadius,if_neg (Nat.not_odd_iff_even.mpr he)]

lemma majorArcs_eq_indexed_balls (r : ℕ) (x : ℝ) :
    majorArcs 8 r x = ⋃ i ∈ actualArcIndices r,
      ball ((i.2:ℝ)/(i.1:ℝ) : AddCircle (1:ℝ)) (actualArcRadius r i.1 x) := by
  ext α
  constructor
  · rintro ⟨q,a,hq,ha,hcop,h⟩
    have hi : (⟨q,a⟩ : Σ _ : ℕ,ℕ) ∈ actualArcIndices r := by
      apply (actualArcIndices_mem r _).mpr
      exact ⟨hq,ha,hcop,h.elim (fun hh => Or.inl ⟨hh.1,hh.2.1⟩)
        (fun hh => Or.inr ⟨hh.1,hh.2.1⟩)⟩
    apply mem_iUnion.mpr
    refine ⟨⟨q,a⟩,mem_iUnion.mpr ⟨hi,?_⟩⟩
    apply mem_ball.mpr
    rcases h with ⟨ho,hqr,hα⟩ | ⟨he,hqr,hα⟩
    · simpa only [actualArcRadius_odd r q x ho] using hα
    · simpa only [actualArcRadius_even r q x he] using hα
  · intro hα
    rcases mem_iUnion.mp hα with ⟨i,hα⟩
    rcases mem_iUnion.mp hα with ⟨hi,hα⟩
    rcases (actualArcIndices_mem r i).mp hi with ⟨hq,ha,hcop,h⟩
    refine ⟨i.1,i.2,hq,ha,hcop,?_⟩
    have hd := mem_ball.mp hα
    rcases h with ⟨ho,hqr⟩ | ⟨he,hqr⟩
    · exact Or.inl ⟨ho,hqr,by simpa only [actualArcRadius_odd r i.1 x ho] using hd⟩
    · exact Or.inr ⟨he,hqr,by simpa only [actualArcRadius_even r i.1 x he] using hd⟩

lemma actualArcRadius_bounds (r q : ℕ) (x : ℝ) (hr : 0 < r) (hq : 0 < q)
    (hx : 32*(r:ℝ)^2 < x) :
    0 ≤ actualArcRadius r q x ∧ actualArcRadius r q x ≤ (1/2:ℝ) ∧
      actualArcRadius r q x ≤ 8*(r:ℝ)/((q:ℝ)*x) := by
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hqone : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hupper : actualArcRadius r q x ≤ 8*(r:ℝ)/((q:ℝ)*x) := by
    unfold actualArcRadius
    split_ifs <;> apply div_le_div_of_nonneg_right _ (by positivity) <;> nlinarith
  have hhalf : 8*(r:ℝ)/((q:ℝ)*x) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (mul_pos hqR hxR)).mpr
    have hqx : x ≤ (q:ℝ)*x := by nlinarith
    have hrsq : (r:ℝ) ≤ (r:ℝ)^2 := by nlinarith
    nlinarith
  refine ⟨?_,hupper.trans hhalf,hupper⟩
  unfold actualArcRadius
  split_ifs <;> positivity

lemma actualArcBalls_pairwise (r : ℕ) (x : ℝ) (hr : 0 < r) (hx : 32*(r:ℝ)^2 < x) :
    Set.Pairwise (↑(actualArcIndices r)) (Disjoint on (fun i : Σ _ : ℕ,ℕ =>
      ball ((i.2:ℝ)/(i.1:ℝ) : AddCircle (1:ℝ)) (actualArcRadius r i.1 x))) := by
  intro i hi j hj hij
  rcases (actualArcIndices_mem r i).mp hi with ⟨hqi,hai,hcopi,hri⟩
  rcases (actualArcIndices_mem r j).mp hj with ⟨hqj,haj,hcopj,hrj⟩
  have hri' : i.1 ≤ 2*r := by rcases hri with h | h <;> omega
  have hrj' : j.1 ≤ 2*r := by rcases hrj with h | h <;> omega
  have hne : (i.2,i.1) ≠ (j.2,j.1) := by
    intro he
    have hq : i.1 = j.1 := congrArg Prod.snd he
    have ha : i.2 = j.2 := congrArg Prod.fst he
    exact hij (Sigma.ext hq (by simpa using ha))
  have hd := major_arc_balls_disjoint hqi hqj hai haj hcopi hcopj hri' hrj' hx hne
  exact hd.mono (ball_subset_ball (actualArcRadius_bounds r i.1 x hr hqi hx).2.2)
    (ball_subset_ball (actualArcRadius_bounds r j.1 x hr hqj hx).2.2)

lemma actualArcRadius_scaled (r q : ℕ) (x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    x*actualArcRadius r q x =
      (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)) := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold actualArcRadius
  split_ifs <;> field_simp

theorem major_arc_integral_decomposition (r : ℕ) (x : ℝ) (hr : 0 < r)
    (hx : 32*(r:ℝ)^2 < x) (f : AddCircle (1:ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) :
    (∫ α in majorArcs 8 r x,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∑ q ∈ actualArcDenominators r,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ β in Set.Icc (-(if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)))
            (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)),
            f (((a:ℝ)/(q:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := by
  classical
  have hxR : 0 < x := lt_of_le_of_lt (by positivity) hx
  rw [majorArcs_eq_indexed_balls]
  rw [integral_biUnion_finset (actualArcIndices r) (fun i hi => measurableSet_ball)
    (actualArcBalls_pairwise r x hr hx) (fun i hi => hf.integrableOn)]
  have he (i : Σ _ : ℕ,ℕ) (hi : i ∈ actualArcIndices r) :
      (∫ α in ball ((i.2:ℝ)/(i.1:ℝ) : AddCircle (1:ℝ)) (actualArcRadius r i.1 x),
        f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∫ β in Set.Icc (-(if Odd i.1 then 4*(r:ℝ)/(i.1:ℝ) else 8*(r:ℝ)/(i.1:ℝ)))
        (if Odd i.1 then 4*(r:ℝ)/(i.1:ℝ) else 8*(r:ℝ)/(i.1:ℝ)),
        f (((i.2:ℝ)/(i.1:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := by
    have hq := ((actualArcIndices_mem r i).mp hi).1
    have hb := actualArcRadius_bounds r i.1 x hr hq hx
    simpa only [actualArcRadius_scaled r i.1 x hq hxR] using
      circle_arc_integral_scaled f ((i.2:ℝ)/(i.1:ℝ)) (actualArcRadius r i.1 x) x hb.1 hb.2.1 hxR
  rw [Finset.sum_congr rfl he,← Finset.smul_sum]
  simp only [actualArcIndices,Finset.sum_sigma]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators

namespace Helfgott

lemma actual_denominators_bounds_arithmetic (q : ℕ) (hq : q ∈ actualArcDenominators 150000) :
    0 < q ∧ q ≤ 300000 := by
  classical
  rcases mem_union.mp hq with hq | hq
  · have h := mem_Icc.mp (mem_filter.mp hq).1
    omega
  · have h := mem_Icc.mp (mem_filter.mp hq).1
    omega

lemma actual_denominators_card_arithmetic : (actualArcDenominators 150000).card ≤ 300000 := by
  classical
  have hs : actualArcDenominators 150000 ⊆ Finset.Icc 1 300000 := by
    intro q hq
    have h := actual_denominators_bounds_arithmetic q hq
    exact mem_Icc.mpr ⟨h.1, h.2⟩
  simpa using Finset.card_le_card hs


lemma inverse_totient_doubling_block (Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Ico Q (2*Q), 1/(Nat.totient q : ℝ)) ≤ 16/5 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h2 : (∑ q ∈ Ico Q (2*Q), 1/(Nat.totient q : ℝ)^2) ≤ 10/(Q : ℝ) := by
    simpa only [two_mul] using SingularAux.inverse_totient_square_finite_tail Q Q hQ
  have hC := sum_mul_sq_le_sq_mul_sq (Ico Q (2*Q))
    (fun q => 1/(Nat.totient q : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hC
  have he : (∑ q ∈ Ico Q (2*Q), (1/(Nat.totient q : ℝ))^2) =
      ∑ q ∈ Ico Q (2*Q), 1/(Nat.totient q : ℝ)^2 := by
    apply sum_congr rfl
    intro q hq
    rw [div_pow, one_pow]
  rw [he] at hC
  have hcard : ((Ico Q (2*Q)).card : ℝ) = Q := by
    simp only [Nat.card_Ico]
    congr 1
    omega
  rw [hcard] at hC
  have hm := mul_le_mul_of_nonneg_right h2 hQR.le
  have hcancel : (10/(Q : ℝ))*(Q : ℝ) = 10 := div_mul_cancel₀ _ hQR.ne'
  rw [hcancel] at hm
  nlinarith

lemma harmonic_doubling_block (Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Ico Q (2*Q), 1/(q : ℝ)) ≤ 1 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  calc
    _ ≤ ∑ _q ∈ Ico Q (2*Q), 1/(Q : ℝ) := by
      apply sum_le_sum
      intro q hq
      have hQq : (Q : ℝ) ≤ q := by exact_mod_cast (mem_Ico.mp hq).1
      exact div_le_div_of_nonneg_left (by norm_num) hQR hQq
    _ = 1 := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Ico]
      have he : 2*Q-Q = Q := by omega
      rw [he]
      field_simp

lemma inverse_totient_dyadic_initial (m : ℕ) :
    (∑ q ∈ Ico (1 : ℕ) ((2 : ℕ)^m), 1/(Nat.totient q : ℝ)) ≤ (16/5 : ℝ)*m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : 0 < (2 : ℕ)^m := pow_pos (by norm_num) _
    have h1 : 1 ≤ (2 : ℕ)^m := hpow
    have h2 : (2 : ℕ)^m ≤ 2*(2 : ℕ)^m := by omega
    rw [pow_succ, Nat.mul_comm (2^m) 2,
      ← sum_Ico_consecutive _ h1 h2]
    have hb := inverse_totient_doubling_block (2^m) hpow
    push_cast
    linarith

lemma harmonic_dyadic_initial (m : ℕ) :
    (∑ q ∈ Ico (1 : ℕ) ((2 : ℕ)^m), 1/(q : ℝ)) ≤ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : 0 < (2 : ℕ)^m := pow_pos (by norm_num) _
    have h1 : 1 ≤ (2 : ℕ)^m := hpow
    have h2 : (2 : ℕ)^m ≤ 2*(2 : ℕ)^m := by omega
    rw [pow_succ, Nat.mul_comm (2^m) 2,
      ← sum_Ico_consecutive _ h1 h2]
    have hb := harmonic_doubling_block (2^m) hpow
    push_cast
    linarith

theorem actual_denominators_inverse_totient_sum_sharp :
    (∑ q ∈ actualArcDenominators 150000, 1/(Nat.totient q : ℝ)) ≤ 64 := by
  have hs : actualArcDenominators 150000 ⊆ Ico (1 : ℕ) ((2 : ℕ)^19) := by
    intro q hq
    have h := actual_denominators_bounds_arithmetic q hq
    refine mem_Ico.mpr ⟨h.1, ?_⟩
    norm_num
    omega
  have hb := inverse_totient_dyadic_initial 19
  refine (sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => by positivity)).trans ?_
  exact hb.trans (by norm_num)

theorem actual_denominators_harmonic_sum_sharp :
    (∑ q ∈ actualArcDenominators 150000, 1/(q : ℝ)) ≤ 19 := by
  have hs : actualArcDenominators 150000 ⊆ Ico (1 : ℕ) ((2 : ℕ)^19) := by
    intro q hq
    have h := actual_denominators_bounds_arithmetic q hq
    refine mem_Ico.mpr ⟨h.1, ?_⟩
    norm_num
    omega
  refine (sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => by positivity)).trans ?_
  simpa using harmonic_dyadic_initial 19

theorem actual_denominators_radius_moments_sharp :
    let D := actualArcDenominators 150000
    let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
    (∑ q ∈ D, 2*R q) ≤ 50000000 ∧
      (∑ q ∈ D, (Nat.totient q : ℝ)*(2*R q)) ≤ 720000000000 := by
  classical
  dsimp only
  let D := actualArcDenominators 150000
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  have hR (q : ℕ) (hq : q ∈ D) : 2*R q ≤ 2400000/(q : ℝ) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (actual_denominators_bounds_arithmetic q hq).1
    dsimp only [R]
    split_ifs <;> apply (le_div_iff₀ hq0).mpr <;> field_simp <;> norm_num
  have hφ (q : ℕ) (hq : q ∈ D) : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (actual_denominators_bounds_arithmetic q hq).1
  have hφq (q : ℕ) : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  constructor
  · calc
      _ ≤ ∑ q ∈ actualArcDenominators 150000, 2400000*(1/(q : ℝ)) := by
        apply sum_le_sum
        intro q hq
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (actual_denominators_bounds_arithmetic q hq).1
        rw [mul_one_div]
        split_ifs <;> apply (le_div_iff₀ hq0).mpr <;> field_simp <;> norm_num
      _ = 2400000*(∑ q ∈ actualArcDenominators 150000, 1/(q : ℝ)) :=
        (mul_sum _ _ _).symm
      _ ≤ 50000000 := by linarith [actual_denominators_harmonic_sum_sharp]
  · calc
      (∑ q ∈ D, (Nat.totient q : ℝ)*(2*R q)) ≤ ∑ q ∈ D, (2400000 : ℝ) := by
        apply sum_le_sum
        intro q hq
        have hq0 : (0 : ℝ) < q := by exact_mod_cast (actual_denominators_bounds_arithmetic q hq).1
        refine (mul_le_mul_of_nonneg_left (hR q hq) (hφ q hq).le).trans ?_
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hq0).mpr
        nlinarith [hφq q]
      _ = (D.card : ℝ)*2400000 := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ 720000000000 := by
        have hc : (D.card : ℝ) ≤ 300000 := by exact_mod_cast actual_denominators_card_arithmetic
        linarith


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace Helfgott.SingularAux
lemma weighted_inverse_totient_initial (X : ℕ) :
    (∑ q ∈ Icc 1 X,(q : ℝ)/(Nat.totient q : ℝ)^2)≤
      5*(∑ q ∈ Icc 1 X,1/(q : ℝ)) := by
  classical
  let s := Icc 1 X
  let a := s.sigma (fun q => q.divisors)
  let f : (Σ _ : ℕ,ℕ) → ℕ×ℕ := fun x => (x.2,x.1/x.2)
  have hprod : ∀ x ∈ a,x.2*(x.1/x.2)=x.1 := by
    intro x hx
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2)
  have hinj : Set.InjOn f (↑a) := by
    intro x hx y hy hxy
    have hd : x.2=y.2 := congrArg Prod.fst hxy
    have hk : x.1/x.2=y.1/y.2 := congrArg Prod.snd hxy
    have hq : x.1=y.1 := by rw [←hprod x hx,←hprod y hy]; exact congrArg₂ Nat.mul hd hk
    exact Sigma.ext hq (by simpa using hd)
  have hsub : a.image f⊆s×ˢs := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
    obtain ⟨hq,hd⟩ := mem_sigma.mp hx
    have hq0 : 0<x.1 := (mem_Icc.mp hq).1
    have hd0 : 0<x.2 := Nat.pos_of_mem_divisors hd
    have hdle : x.2≤x.1 := Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors hd)
    have hk0 : 0<x.1/x.2 := Nat.div_pos hdle hd0
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hd0,hdle.trans (mem_Icc.mp hq).2⟩,
      mem_Icc.mpr ⟨hk0,(Nat.div_le_self x.1 x.2).trans (mem_Icc.mp hq).2⟩⟩
  let G : ℕ×ℕ → ℝ := fun b => totientWeight b.1/(b.2 : ℝ)
  have he : (∑ q ∈ s,(q : ℝ)/(Nat.totient q : ℝ)^2)=∑ x ∈ a,G (f x) := by
    dsimp only [a]
    rw [sum_sigma]
    apply sum_congr rfl
    intro q hq
    have hqp : 0<q := (mem_Icc.mp hq).1
    rw [show (q : ℝ)/(Nat.totient q : ℝ)^2=(q : ℝ)*(1/(Nat.totient q : ℝ)^2) by ring,
      inverse_totient_square_divisor_expansion q hqp.ne',mul_sum]
    apply sum_congr rfl
    intro d hd
    have hdp : 0<d := Nat.pos_of_mem_divisors hd
    have hkp : 0<q/d := Nat.div_pos (Nat.le_of_dvd hqp (Nat.dvd_of_mem_divisors hd)) hdp
    have hdc : (d : ℝ)≠0 := by exact_mod_cast hdp.ne'
    have hkc : ((q/d : ℕ) : ℝ)≠0 := by exact_mod_cast hkp.ne'
    have hmul : (d : ℝ)*((q/d : ℕ) : ℝ)=(q : ℝ) := by exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    dsimp [G,f]
    rw [←hmul]
    field_simp
  have hW : (∑ d ∈ s,totientWeight d)≤5 :=
    (totientWeight_summable.sum_le_tsum s (fun d _ => totientWeight_nonneg d)).trans totientWeight_tsum_upper
  have hH : 0≤∑ q ∈ s,1/(q : ℝ) := sum_nonneg (fun q _ => by positivity)
  calc
    _=∑ x ∈ a,G (f x) := he
    _=∑ b ∈ a.image f,G b := (sum_image hinj).symm
    _≤∑ b ∈ s×ˢs,G b := sum_le_sum_of_subset_of_nonneg hsub
      (fun b _ _ => div_nonneg (totientWeight_nonneg _) (Nat.cast_nonneg _))
    _=(∑ d ∈ s,totientWeight d)*(∑ q ∈ s,1/(q : ℝ)) := by
      rw [sum_product]
      dsimp [G]
      simp_rw [div_eq_mul_inv,←mul_sum]
      rw [sum_mul]
      simp only [one_mul]
    _≤5*(∑ q ∈ s,1/(q : ℝ)) := mul_le_mul_of_nonneg_right hW hH

lemma harmonic_300000_le_fourteen : (∑ q ∈ Icc (1 : ℕ) 300000,1/(q : ℝ))≤14 := by
  have h := harmonic_le_one_add_log 300000
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤271/100)
    (show (271/100 : ℝ)≤Real.exp 1 by linarith [Real.exp_one_gt_d9]) 13
  rw [←Real.exp_nat_mul,mul_one] at hpow
  have hnum : (300000 : ℝ)≤(271/100 : ℝ)^13 := by norm_num
  have hlog := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ)<300000)).mpr (hnum.trans hpow)
  norm_num only [Nat.cast_ofNat] at h hlog
  simpa only [one_div] using h.trans (by linarith)

lemma inverse_totient_300000_le_thirtytwo :
    (∑ q ∈ Icc (1 : ℕ) 300000,1/(Nat.totient q : ℝ))≤32 := by
  let s := Icc (1 : ℕ) 300000
  have h := sum_mul_sq_le_sq_mul_sq s
    (fun q => Real.sqrt q/(Nat.totient q : ℝ)) (fun q => 1/Real.sqrt q)
  have he1 : (∑ q ∈ s,(Real.sqrt q/(Nat.totient q : ℝ))*(1/Real.sqrt q))=
      ∑ q ∈ s,1/(Nat.totient q : ℝ) := by
    apply sum_congr rfl
    intro q hq
    have hqp : (0 : ℝ)<q := by exact_mod_cast (mem_Icc.mp hq).1
    field_simp
  have he2 : (∑ q ∈ s,(Real.sqrt q/(Nat.totient q : ℝ))^2)=
      ∑ q ∈ s,(q : ℝ)/(Nat.totient q : ℝ)^2 := by
    apply sum_congr rfl
    intro q _
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg q)]
  have he3 : (∑ q ∈ s,(1/Real.sqrt q)^2)=∑ q ∈ s,1/(q : ℝ) := by
    apply sum_congr rfl
    intro q _
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg q),one_pow]
  rw [he1,he2,he3] at h
  have hH := harmonic_300000_le_fourteen
  have hW := weighted_inverse_totient_initial 300000
  have hH0 : 0≤∑ q ∈ s,1/(q : ℝ) := sum_nonneg (fun q _ => by positivity)
  have hW0 : 0≤∑ q ∈ s,(q : ℝ)/(Nat.totient q : ℝ)^2 := sum_nonneg (fun q _ => by positivity)
  have hm := mul_le_mul hW hH hH0 (by norm_num; positivity : (0 : ℝ)≤5*(∑ q ∈ s,1/(q : ℝ)))
  nlinarith
end Helfgott.SingularAux
namespace Helfgott
theorem actual_denominators_inverse_totient_sum_tight :
    (∑ q ∈ actualArcDenominators 150000,1/(Nat.totient q : ℝ))≤32 := by
  refine (sum_le_sum_of_subset_of_nonneg (s := actualArcDenominators 150000)
    (t := Icc (1 : ℕ) 300000) ?_ (fun q _ _ => by positivity)).trans
      SingularAux.inverse_totient_300000_le_thirtytwo
  intro q hq
  exact mem_Icc.mpr (actual_denominators_bounds_arithmetic q hq)
theorem actual_denominators_width_sum_tight :
    (∑ q ∈ actualArcDenominators 150000,2*(if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)))≤33600000 := by
  have hpoint (q : ℕ) : 2*(if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ))≤2400000/(q : ℝ) := by
    split_ifs <;> simp only [div_eq_mul_inv] <;> nlinarith [inv_nonneg.mpr (Nat.cast_nonneg q : (0 : ℝ)≤q)]
  have hsub : actualArcDenominators 150000⊆Icc (1 : ℕ) 300000 := by
    intro q hq
    exact mem_Icc.mpr (actual_denominators_bounds_arithmetic q hq)
  calc
    _≤∑ q ∈ actualArcDenominators 150000,2400000/(q : ℝ) := sum_le_sum (fun q _ => hpoint q)
    _≤∑ q ∈ Icc (1 : ℕ) 300000,2400000/(q : ℝ) := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _=2400000*(∑ q ∈ Icc (1 : ℕ) 300000,1/(q : ℝ)) := by rw [mul_sum]; apply sum_congr rfl; intro q _; ring
    _≤33600000 := by nlinarith [SingularAux.harmonic_300000_le_fourteen]
end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Finset Filter
open scoped BigOperators Topology
namespace Helfgott.SingularAux
lemma totientLocal_even_tail_zero (n : ℕ) : totientLocal (2*n+32)=0 := by
  have he : Even (2*n+32) := ⟨n+16,by omega⟩
  have hp : ¬Nat.Prime (2*n+32) := by
    intro h; have hh := h.even_iff.mp he; omega
  simp [totientLocal,hp]
lemma totientLocal_odd_tail_step (n : ℕ) :
    totientLocal (2*n+33)≤(3/2 : ℝ)/((2*n : ℝ)+31)-(3/2 : ℝ)/((2*n : ℝ)+33) := by
  have h := totientLocal_telescoping (p := 2*n+33) (by omega)
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h
  have hpos : (0 : ℝ)<2*n+31 := by positivity
  have he : 3/((2*n : ℝ)+33-1)-3/((2*n : ℝ)+33) =
      3/(((2*n : ℝ)+32)*((2*n : ℝ)+33)) := by
    rw [show (2*n : ℝ)+33-1=2*n+32 by ring]
    field_simp
    ring
  have he' : (3/2 : ℝ)/((2*n : ℝ)+31)-(3/2 : ℝ)/((2*n : ℝ)+33) =
      3/(((2*n : ℝ)+31)*((2*n : ℝ)+33)) := by field_simp; ring
  rw [he] at h; rw [he']
  refine h.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_)
  nlinarith
lemma totientLocal_paired_tail_sum (n : ℕ) :
    (∑ k ∈ range (2*n),totientLocal (k+32))≤3/62-(3/2 : ℝ)/((2*n : ℝ)+31) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,sum_range_add]
    norm_num only [sum_range_succ,sum_range_zero,Nat.add_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [totientLocal_even_tail_zero]
    have h := totientLocal_odd_tail_step n
    have he : 2*n+1+32=2*n+33 := by omega
    rw [he,show (2 : ℝ)*((n : ℝ)+1)+31=2*n+33 by ring]
    linarith
lemma totientLocal_tail_sum_tight (n : ℕ) : (∑ k ∈ range n,totientLocal (k+32))≤3/62 := by
  have hle : (∑ k ∈ range n,totientLocal (k+32))≤∑ k ∈ range (2*n),totientLocal (k+32) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun k _ _ => totientLocal_nonneg _)
  have h := totientLocal_paired_tail_sum n
  have hn : (0 : ℝ)≤(3/2 : ℝ)/((2*n : ℝ)+31) := by positivity
  linarith
lemma totientLocal_tail_prod_tight (n : ℕ) : (∏ k ∈ range n,(1+totientLocal (k+32)))≤62/59 := by
  have hs := totientLocal_tail_sum_tight n
  have hp : 0≤∏ k ∈ range n,(1+totientLocal (k+32)) := prod_nonneg (fun k _ => by linarith [totientLocal_nonneg (k+32)])
  have hh := prod_one_add_times_one_sub_sum_le (range n) (fun k => totientLocal (k+32)) (fun k _ => totientLocal_nonneg _)
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hs)]
lemma totientLocal_partial_prod_tight (Q : ℕ) : (∏ p ∈ range Q,(1+totientLocal p))≤14/3 := by
  by_cases hQ : Q≤32
  · have hle : (∏ p ∈ range Q,(1+totientLocal p))≤∏ p ∈ range 32,(1+totientLocal p) := by
      apply prod_le_prod_of_subset_of_one_le (range_mono hQ)
      · intro p _;linarith [totientLocal_nonneg p]
      · intro p _ _;linarith [totientLocal_nonneg p]
    linarith [totientLocal_prefix_prod]
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 32≤Q)
    rw [prod_range_add]
    have ht : (∏ k ∈ range n,(1+totientLocal (32+k)))≤62/59 := by simpa only [Nat.add_comm] using totientLocal_tail_prod_tight n
    have hn : 0≤∏ k ∈ range n,(1+totientLocal (32+k)) := prod_nonneg (fun k _ => by linarith [totientLocal_nonneg (32+k)])
    have h := mul_le_mul totientLocal_prefix_prod ht hn (by norm_num : (0 : ℝ)≤22/5)
    linarith
lemma totientWeight_tsum_tight : (∑' n : ℕ,totientWeight n)≤14/3 := by
  have hnorm : Summable (fun n : ℕ => ‖totientWeight n‖) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (totientWeight_nonneg _)] using totientWeight_summable
  have he := EulerProduct.eulerProduct_hasProd_mulIndicator totientWeight_one
    (fun {m n} h => totientWeight_mul h) hnorm totientWeight_zero
  have hf : Set.mulIndicator {p : ℕ | Nat.Prime p}
      (fun p => ∑' k : ℕ,totientWeight (p^k))=(fun p : ℕ => 1+totientLocal p) := by
    funext p;by_cases hp : Nat.Prime p
    · simp only [Set.mulIndicator_of_mem (show p∈{p : ℕ | Nat.Prime p} from hp)];exact totientWeight_prime_pow_tsum hp
    · simp [Set.mulIndicator_of_notMem,hp,totientLocal]
  rw [hf] at he
  rw [←he.tprod_eq]
  exact le_of_tendsto totientLocal_multipliable.tendsto_prod_tprod_nat (Eventually.of_forall totientLocal_partial_prod_tight)
end Helfgott.SingularAux
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
open Finset
open scoped BigOperators
namespace Helfgott.SingularAux
lemma weighted_inverse_totient_initial_tight (X : ℕ) :
    (∑ q ∈ Icc 1 X,(q : ℝ)/(Nat.totient q : ℝ)^2)≤
      (14/3)*(∑ q ∈ Icc 1 X,1/(q : ℝ)) := by
  classical
  let s := Icc 1 X
  let a := s.sigma (fun q => q.divisors)
  let f : (Σ _ : ℕ,ℕ) → ℕ×ℕ := fun x => (x.2,x.1/x.2)
  have hprod : ∀ x ∈ a,x.2*(x.1/x.2)=x.1 := by
    intro x hx
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors (mem_sigma.mp hx).2)
  have hinj : Set.InjOn f (↑a) := by
    intro x hx y hy hxy
    have hd : x.2=y.2 := congrArg Prod.fst hxy
    have hk : x.1/x.2=y.1/y.2 := congrArg Prod.snd hxy
    have hq : x.1=y.1 := by rw [←hprod x hx,←hprod y hy]; exact congrArg₂ Nat.mul hd hk
    exact Sigma.ext hq (by simpa using hd)
  have hsub : a.image f⊆s×ˢs := by
    intro b hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
    obtain ⟨hq,hd⟩ := mem_sigma.mp hx
    have hq0 : 0<x.1 := (mem_Icc.mp hq).1
    have hd0 : 0<x.2 := Nat.pos_of_mem_divisors hd
    have hdle : x.2≤x.1 := Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors hd)
    have hk0 : 0<x.1/x.2 := Nat.div_pos hdle hd0
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hd0,hdle.trans (mem_Icc.mp hq).2⟩,
      mem_Icc.mpr ⟨hk0,(Nat.div_le_self x.1 x.2).trans (mem_Icc.mp hq).2⟩⟩
  let G : ℕ×ℕ → ℝ := fun b => totientWeight b.1/(b.2 : ℝ)
  have he : (∑ q ∈ s,(q : ℝ)/(Nat.totient q : ℝ)^2)=∑ x ∈ a,G (f x) := by
    dsimp only [a]
    rw [sum_sigma]
    apply sum_congr rfl
    intro q hq
    have hqp : 0<q := (mem_Icc.mp hq).1
    rw [show (q : ℝ)/(Nat.totient q : ℝ)^2=(q : ℝ)*(1/(Nat.totient q : ℝ)^2) by ring,
      inverse_totient_square_divisor_expansion q hqp.ne',mul_sum]
    apply sum_congr rfl
    intro d hd
    have hdp : 0<d := Nat.pos_of_mem_divisors hd
    have hkp : 0<q/d := Nat.div_pos (Nat.le_of_dvd hqp (Nat.dvd_of_mem_divisors hd)) hdp
    have hdc : (d : ℝ)≠0 := by exact_mod_cast hdp.ne'
    have hkc : ((q/d : ℕ) : ℝ)≠0 := by exact_mod_cast hkp.ne'
    have hmul : (d : ℝ)*((q/d : ℕ) : ℝ)=(q : ℝ) := by exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    dsimp [G,f]
    rw [←hmul]
    field_simp
  have hW : (∑ d ∈ s,totientWeight d)≤14/3 :=
    (totientWeight_summable.sum_le_tsum s (fun d _ => totientWeight_nonneg d)).trans totientWeight_tsum_tight
  have hH : 0≤∑ q ∈ s,1/(q : ℝ) := sum_nonneg (fun q _ => by positivity)
  calc
    _=∑ x ∈ a,G (f x) := he
    _=∑ b ∈ a.image f,G b := (sum_image hinj).symm
    _≤∑ b ∈ s×ˢs,G b := sum_le_sum_of_subset_of_nonneg hsub
      (fun b _ _ => div_nonneg (totientWeight_nonneg _) (Nat.cast_nonneg _))
    _=(∑ d ∈ s,totientWeight d)*(∑ q ∈ s,1/(q : ℝ)) := by
      rw [sum_product]
      dsimp [G]
      simp_rw [div_eq_mul_inv,←mul_sum]
      rw [sum_mul]
      simp only [one_mul]
    _≤(14/3)*(∑ q ∈ s,1/(q : ℝ)) := mul_le_mul_of_nonneg_right hW hH


lemma harmonic_300000_le_thirteen_seven : (∑ q ∈ Icc (1 : ℕ) 300000,1/(q : ℝ))≤137/10 := by
  have h := harmonic_le_one_add_log 300000
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at h
  norm_num only [Nat.cast_ofNat] at h
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤271/100)
    (show (271/100 : ℝ)≤Real.exp 1 by linarith [Real.exp_one_gt_d9]) 12
  rw [←Real.exp_nat_mul,mul_one] at hpow
  have hs := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤7/10)
  have hm := mul_le_mul hpow hs (by norm_num : (0 : ℝ)≤1+7/10+(7/10)^2/2)
    (Real.exp_pos _).le
  rw [←Real.exp_add] at hm
  have hn : (300000 : ℝ)≤(271/100 : ℝ)^12*(1+7/10+(7/10)^2/2) := by norm_num
  have hl := (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ)<300000)).mpr (hn.trans hm)
  norm_num only [Nat.cast_ofNat] at hl
  simpa only [one_div] using h.trans (by linarith)
lemma inverse_totient_300000_le_thirty :
    (∑ q ∈ Icc (1 : ℕ) 300000,1/(Nat.totient q : ℝ))≤30 := by
  let s := Icc (1 : ℕ) 300000
  have h := sum_mul_sq_le_sq_mul_sq s (fun q => Real.sqrt q/(Nat.totient q : ℝ)) (fun q => 1/Real.sqrt q)
  have he1 : (∑ q ∈ s,(Real.sqrt q/(Nat.totient q : ℝ))*(1/Real.sqrt q))=∑ q ∈ s,1/(Nat.totient q : ℝ) := by
    apply sum_congr rfl;intro q hq
    have hqp : (0 : ℝ)<q := by exact_mod_cast (mem_Icc.mp hq).1
    field_simp
  have he2 : (∑ q ∈ s,(Real.sqrt q/(Nat.totient q : ℝ))^2)=∑ q ∈ s,(q : ℝ)/(Nat.totient q : ℝ)^2 := by
    apply sum_congr rfl;intro q _;rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg q)]
  have he3 : (∑ q ∈ s,(1/Real.sqrt q)^2)=∑ q ∈ s,1/(q : ℝ) := by
    apply sum_congr rfl;intro q _;rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg q),one_pow]
  rw [he1,he2,he3] at h
  have hh := harmonic_300000_le_thirteen_seven
  have hw := weighted_inverse_totient_initial_tight 300000
  have hh0 : 0≤∑ q ∈ s,1/(q : ℝ) := sum_nonneg (fun q _ => by positivity)
  have hm := mul_le_mul hw hh hh0 (by positivity : (0 : ℝ)≤(14/3)*(∑ q ∈ s,1/(q : ℝ)))
  nlinarith
end Helfgott.SingularAux
namespace Helfgott
theorem actual_denominators_inverse_totient_sum_cauchy_tight :
    (∑ q ∈ actualArcDenominators 150000,1/(Nat.totient q : ℝ))≤30 := by
  refine (sum_le_sum_of_subset_of_nonneg (s := actualArcDenominators 150000) (t := Icc (1 : ℕ) 300000)
    ?_ (fun q _ _ => by positivity)).trans SingularAux.inverse_totient_300000_le_thirty
  intro q hq;exact mem_Icc.mpr (actual_denominators_bounds_arithmetic q hq)
end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
open Finset
open scoped BigOperators
namespace Helfgott.SingularAux
lemma reciprocal_sqrt_step (k : ℕ) :
    1/Real.sqrt ((k : ℝ)+1)≤2*(Real.sqrt ((k : ℝ)+1)-Real.sqrt k) := by
  have hk : (0 : ℝ)≤k := Nat.cast_nonneg k
  have hp : (0 : ℝ)<(k : ℝ)+1 := by positivity
  have hroot := Real.sq_sqrt hp.le
  have hprev := Real.sq_sqrt hk
  have hrp := Real.sqrt_pos.mpr hp
  apply (div_le_iff₀ hrp).mpr
  nlinarith [sq_nonneg (Real.sqrt ((k : ℝ)+1)-Real.sqrt k)]
lemma reciprocal_sqrt_initial (X : ℕ) :
    (∑ q ∈ Icc (1 : ℕ) X,1/Real.sqrt q)≤2*Real.sqrt X := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h := reciprocal_sqrt_step X
    norm_num only [Nat.cast_succ] at *
    linarith
end Helfgott.SingularAux
namespace Helfgott
theorem actual_denominators_sqrt_width_sum_tight :
    (∑ q ∈ actualArcDenominators 150000,
      Real.sqrt (2*(if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ))))≤1700000 := by
  classical
  let D := actualArcDenominators 150000
  let W (q : ℕ) : ℝ := 2*(if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ))
  have hp (q : ℕ) (hq : 0<q) : Real.sqrt (W q)≤1550/Real.sqrt q := by
    have hqp : (0 : ℝ)<q := by exact_mod_cast hq
    have hw0 : 0≤W q := by dsimp only [W];split_ifs <;> positivity
    have hw : W q≤2400000/(q : ℝ) := by
      dsimp only [W];split_ifs <;> simp only [div_eq_mul_inv] <;> nlinarith [inv_nonneg.mpr hqp.le]
    have hm := (le_div_iff₀ hqp).mp hw
    have he : (Real.sqrt (W q)*Real.sqrt q)^2=W q*(q : ℝ) := by
      rw [mul_pow,Real.sq_sqrt hw0,Real.sq_sqrt hqp.le]
    have hb : Real.sqrt (W q)*Real.sqrt q≤1550 := by
      apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by norm_num : (0 : ℝ)≤1550)).mp
      rw [he];linarith
    exact (le_div_iff₀ (Real.sqrt_pos.mpr hqp)).mpr hb
  have hsub : D⊆Icc (1 : ℕ) 300000 := by
    intro q hq;exact mem_Icc.mpr (actual_denominators_bounds_arithmetic q hq)
  have hs : (∑ q ∈ D,Real.sqrt (W q))≤1550*(∑ q ∈ Icc (1 : ℕ) 300000,1/Real.sqrt q) := by
    calc
      _≤∑ q ∈ D,1550/Real.sqrt q := sum_le_sum (fun q hq => hp q (actual_denominators_bounds_arithmetic q hq).1)
      _≤∑ q ∈ Icc (1 : ℕ) 300000,1550/Real.sqrt q := sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
      _=_ := by rw [mul_sum];apply sum_congr rfl;intro q _;ring
  have hh := SingularAux.reciprocal_sqrt_initial 300000
  have hr : Real.sqrt (300000 : ℝ)≤548 := by
    apply (Real.sqrt_le_left (by norm_num : (0 : ℝ)≤548)).mpr;norm_num
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤1550)
  change (∑ q ∈ D,Real.sqrt (W q))≤1700000
  norm_num only [Nat.cast_ofNat] at hm
  linarith
end Helfgott
end

section

end

theorem solution :
  let D := (Finset.Icc 1 150000).filter (fun q => Odd q) ∪
    (Finset.Icc 1 300000).filter (fun q => Even q)
  let R : ℕ → ℝ := fun q => if Odd q then 600000/(q : ℝ) else 1200000/(q : ℝ)
  (∑ q ∈ D,1/(Nat.totient q : ℝ))≤30 ∧
  (∑ q ∈ D,2*R q)≤33600000 ∧
  (∑ q ∈ D,Real.sqrt (2*R q))≤1700000 ∧
  (∑ q ∈ D,(Nat.totient q : ℝ)*(2*R q))≤720000000000 := by
  exact ⟨Helfgott.actual_denominators_inverse_totient_sum_cauchy_tight,
    Helfgott.actual_denominators_width_sum_tight,
    Helfgott.actual_denominators_sqrt_width_sum_tight,
    Helfgott.actual_denominators_radius_moments_sharp.2⟩
#print axioms solution
