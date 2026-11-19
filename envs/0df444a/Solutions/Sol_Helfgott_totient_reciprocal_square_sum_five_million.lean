-- Prove2me | solution 1 for Helfgott.totient_reciprocal_square_sum_five_million
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-18T12:15:32.168824+00:00
-- url     : https://prove2.me/submissions/f566e29a-cf81-4b2c-94ca-5a0348652526

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
open Finset
open scoped BigOperators

-- Preserved source: upstream/Solutions/SieveModulusFactors.lean; SHA256 6edd58c864e0422023d01697993db747bbaaa45bb00fadcdd08364c578c7f5e7


open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace SieveModulusFactors

/-- Distinct integers at least two grow at least as fast as consecutive integers. -/
lemma factorial_card_le_prod (F : Finset ℕ) (hF : ∀ p ∈ F, 2 ≤ p) :
    (F.card + 1).factorial ≤ ∏ p ∈ F, p := by
  induction F using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : 2 ≤ a := hF a (mem_insert_self a s)
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hF p (mem_insert_of_mem hp)
    have hnot : a ∉ s := fun h => (hmax a h).false
    have hsub : s ⊆ Ico 2 a := fun p hp => mem_Ico.mpr ⟨hs p hp, hmax p hp⟩
    have hc := card_le_card hsub
    simp only [Nat.card_Ico] at hc
    have hca : s.card + 2 ≤ a := by omega
    rw [card_insert_of_notMem hnot, prod_insert hnot]
    rw [show s.card + 1 + 1 = (s.card + 1) + 1 by omega, Nat.factorial_succ]
    exact Nat.mul_le_mul hca (ih hs)



























lemma totient_ratio_prod (q : ℕ) (hq : 0 < q) :
    (q : ℝ)/(q.totient : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ)/((p : ℝ)-1) := by
  have ht := Nat.totient_mul_prod_primeFactors q
  have htR : (q.totient : ℝ) * (∏ p ∈ q.primeFactors, (p : ℝ)) =
      (q : ℝ) * ∏ p ∈ q.primeFactors, ((p : ℝ)-1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) ht
    push_cast at hcast
    convert hcast using 2
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have htpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hprodpos : 0 < ∏ p ∈ q.primeFactors, ((p : ℝ)-1) := by
    apply prod_pos
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [prod_div_distrib]
  exact (div_eq_div_iff (ne_of_gt htpos) (ne_of_gt hprodpos)).mpr (by linarith)











end SieveModulusFactors


-- Preserved source: upstream/Solutions/FiniteTotientRatioFiveMillion.lean; SHA256 a431d1d9c2ea85f52a317a7e5a4ea5880f6b95fd4a3b092e66094bdc2fef21d6


open Finset
open scoped BigOperators
namespace Helfgott

/-- Eight distinct prime factors already force the product above 5000000. -/
theorem primeFactors_card_le_seven_five_million (q : ℕ) (hq : 0<q) (hmax : q≤5000000) :
    q.primeFactors.card≤7 := by
  classical
  let C : Finset ℕ := {4,6,8,9,10,12,14,15,16,18}
  have hC : ∀ p∈C,2≤p ∧ ¬p.Prime := by decide
  have hd : Disjoint C q.primeFactors := by
    apply disjoint_left.mpr
    intro p hp hq'
    exact (hC p hp).2 (Nat.prime_of_mem_primeFactors hq')
  have hf := SieveModulusFactors.factorial_card_le_prod (C∪q.primeFactors) (by
    intro p hp
    rcases mem_union.mp hp with hc|hq'
    · exact (hC p hc).1
    · exact (Nat.prime_of_mem_primeFactors hq').two_le)
  rw [card_union_of_disjoint hd,prod_union hd] at hf
  have hcard : C.card=10 := by decide
  have hprod : (∏ p∈C,p)=12541132800 := by decide
  rw [hcard,hprod] at hf
  have hrad := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  by_contra hh
  have hfac := Nat.factorial_le (show 19≤10+q.primeFactors.card+1 by omega)
  norm_num at hfac
  omega

private noncomputable def fiveMillionTotientNormalizedFactor (p : ℕ) : ℝ :=
  (16/17)*((p:ℝ)/((p:ℝ)-1))

private theorem fiveMillionTotientNormalizedFactor_large (p : ℕ) (hp : 17≤p) :
    fiveMillionTotientNormalizedFactor p≤1 := by
  have hpR : (17:ℝ)≤p := by exact_mod_cast hp
  have hr : (p:ℝ)/((p:ℝ)-1)≤(17/16:ℝ) :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  unfold fiveMillionTotientNormalizedFactor
  linarith

/-- A seven-factor Euler product is maximized by the first seven primes. -/
theorem totient_ratio_le_17017_div_3072 (q : ℕ) (hq : 0<q) (hmax : q≤5000000) :
    (q:ℝ)/(q.totient:ℝ)≤(17017/3072:ℝ) := by
  classical
  let F : Finset ℕ := {2,3,5,7,11,13}
  let P := q.primeFactors
  have hpos (p : ℕ) (hp : p.Prime) : 0≤fiveMillionTotientNormalizedFactor p := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    have hp1 : 0≤(p:ℝ)-1 := by linarith
    unfold fiveMillionTotientNormalizedFactor
    positivity
  have hsmall (p : ℕ) (hp : p∈F) : 1≤fiveMillionTotientNormalizedFactor p := by
    simp only [F,mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [fiveMillionTotientNormalizedFactor]
  have hbig (p : ℕ) (hp : p∈P) (hn : p∉F) : fiveMillionTotientNormalizedFactor p≤1 := by
    apply fiveMillionTotientNormalizedFactor_large
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_contra hh
    have hlt : p<17 := by omega
    interval_cases p <;> norm_num [F] at *
  have hprod : (∏ p∈P,fiveMillionTotientNormalizedFactor p)≤(∏ p∈F,fiveMillionTotientNormalizedFactor p) := by
    calc
      _ ≤ ∏ p∈P,if p∈F then fiveMillionTotientNormalizedFactor p else 1 := by
        apply prod_le_prod (fun p hp=>hpos p (Nat.prime_of_mem_primeFactors hp))
        intro p hp
        split_ifs with h
        · exact le_rfl
        · exact hbig p hp h
      _ = ∏ p∈P.filter (fun p=>p∈F),fiveMillionTotientNormalizedFactor p := (prod_filter _ _).symm
      _ ≤ ∏ p∈F,fiveMillionTotientNormalizedFactor p :=
        prod_le_prod_of_subset_of_one_le (fun p hp=>(mem_filter.mp hp).2)
          (fun p hp=>le_trans (by norm_num) (hsmall p (mem_filter.mp hp).2)) (fun p hp hn=>hsmall p hp)
  have hcard : P.card≤7 := primeFactors_card_le_seven_five_million q hq hmax
  have heq : (∏ p∈P,(p:ℝ)/((p:ℝ)-1))=
      (17/16:ℝ)^P.card*(∏ p∈P,fiveMillionTotientNormalizedFactor p) := by
    rw [←prod_const,←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    unfold fiveMillionTotientNormalizedFactor
    ring
  rw [SieveModulusFactors.totient_ratio_prod q hq,heq]
  calc
    _ ≤ (17/16:ℝ)^7*(∏ p∈F,fiveMillionTotientNormalizedFactor p) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard) hprod
        (prod_nonneg fun p hp=>hpos p (Nat.prime_of_mem_primeFactors hp)) (by positivity)
    _ = _ := by norm_num [F,fiveMillionTotientNormalizedFactor]

theorem totient_ratio_le_six_five_million (q : ℕ) (hq : 0<q) (hmax : q≤5000000) :
    (q:ℝ)/(q.totient:ℝ)≤6 :=
  (totient_ratio_le_17017_div_3072 q hq hmax).trans (by norm_num)









end Helfgott


-- Preserved source: upstream/Solutions/FiniteTotientReciprocalSquare.lean; SHA256 8985eb43dd77c71d3cf7f2086a3abb91d09f84e619ff3ebbfc797db0312019d3


open Finset
open scoped BigOperators
namespace Helfgott

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem totient_square_first_hundred_rational :
    (∑ q ∈ Finset.Icc 1 100, (1:ℚ)/(q.totient:ℚ)^2) ≤ 7/2 := by
  decide +kernel

/-- A small exact rational computation, transferred to the real numbers. -/
theorem totient_square_first_hundred :
    (∑ q ∈ Finset.Icc 1 100, (1:ℝ)/(q.totient:ℝ)^2) ≤ 7/2 := by
  have h := (Rat.cast_le (K:=ℝ)).mpr totient_square_first_hundred_rational
  push_cast at h
  exact h

/-- Uniform reciprocal-square sum through five million, with a100-term kernel check
and a telescoping tail; no large integer enumeration is used. -/
theorem totient_reciprocal_square_sum_five_million :
    (∑ q ∈ Finset.Icc 1 5000000, (1:ℝ)/(q.totient:ℝ)^2) ≤ 4 := by
  have htail : (∑ q ∈ Finset.Ioc (100:ℕ) 5000000, (1:ℝ)/(q.totient:ℝ)^2) ≤ 36/100 := by
    calc
      _ ≤ ∑ q ∈ Finset.Ioc (100:ℕ) 5000000, 36*((q:ℝ)^2)⁻¹ := by
        apply sum_le_sum
        intro q hq
        have hqN := mem_Ioc.mp hq
        have hq0 : 0 < q := by omega
        have hqR : (0:ℝ) < q := by exact_mod_cast hq0
        have hpR : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq0
        have hr := totient_ratio_le_six_five_million q hq0 hqN.2
        have hi : (1:ℝ)/(q.totient:ℝ) ≤ 6/(q:ℝ) := by
          apply (div_le_div_iff₀ hpR hqR).mpr
          simpa only [one_mul] using (div_le_iff₀ hpR).mp hr
        have hs := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/(q.totient:ℝ)) hi 2
        convert hs using 1 <;> field_simp <;> ring
      _ = 36*(∑ q ∈ Finset.Ioc (100:ℕ) 5000000, ((q:ℝ)^2)⁻¹) := (mul_sum ..).symm
      _ ≤ 36*((100:ℝ)⁻¹-(5000000:ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub (by norm_num) (by norm_num))
        norm_num
      _ ≤ _ := by norm_num
  have he : Finset.Icc 1 5000000=Finset.Icc 1 100 ∪ Finset.Ioc (100:ℕ) 5000000 := by
    ext q
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 100) (Finset.Ioc (100:ℕ) 5000000) := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    have h := mem_Icc.mp hq
    have h' := mem_Ioc.mp hq'
    omega
  rw [he,Finset.sum_union hd]
  linarith [totient_square_first_hundred]



end Helfgott




theorem solution :
    (∑ q ∈ Finset.Icc 1 5000000, (1:ℝ)/(q.totient:ℝ)^2) ≤ 4 := by
  apply Helfgott.totient_reciprocal_square_sum_five_million <;> assumption
