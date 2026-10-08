-- Prove2me | solution 1 for Helfgott.inverse_totient_square_tail
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T02:21:59.361511+00:00
-- url     : https://prove2.me/submissions/c8148c0b-8c4c-458b-a6f1-b661a32ed279

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

/-! Complete quantitative singular-series remainder proof. Written by Codex. -/

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

theorem solution (Q : ℕ) (hQ : 0 < Q) :
    (∑' k : ℕ,1/(Nat.totient (k+Q):ℝ)^2) ≤ 10/(Q:ℝ) := Helfgott.SingularAux.inverse_totient_square_tail Q hQ

#print axioms solution
