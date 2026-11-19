-- Prove2me | solution 1 for Helfgott.totient_ratio_le_1001_div_192
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-18T12:15:22.437322+00:00
-- url     : https://prove2.me/submissions/30dd65b9-e995-42ae-b1d9-e64273700d7e

import Mathlib.Analysis.Complex.ExponentialBounds
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


-- Preserved source: upstream/Solutions/FiniteTotientRatioSharp.lean; SHA256 c6a4df96e42e66116312cc478c5bbab582d21a3a2dca82459003bdc35a49ae60


open Finset
open scoped BigOperators
namespace Helfgott

/-- Seven distinct prime factors already force the product above 300000. -/
theorem primeFactors_card_le_six_finite (q : ℕ) (hq : 0<q) (hmax : q≤300000) :
    q.primeFactors.card≤6 := by
  classical
  let C : Finset ℕ := {4,6,8,9,10,12,14,15,16}
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
  have hcard : C.card=9 := by decide
  have hprod : (∏ p∈C,p)=696729600 := by decide
  rw [hcard,hprod] at hf
  have hrad := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  by_contra hh
  have hfac := Nat.factorial_le (show 17≤9+q.primeFactors.card+1 by omega)
  norm_num at hfac
  omega

private noncomputable def finiteTotientNormalizedFactor (p : ℕ) : ℝ :=
  (12/13)*((p:ℝ)/((p:ℝ)-1))

private theorem finiteTotientNormalizedFactor_large (p : ℕ) (hp : 13≤p) :
    finiteTotientNormalizedFactor p≤1 := by
  have hpR : (13:ℝ)≤p := by exact_mod_cast hp
  have hr : (p:ℝ)/((p:ℝ)-1)≤(13/12:ℝ) :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  unfold finiteTotientNormalizedFactor
  linarith

/-- A six-factor Euler product is maximized by the first six primes. -/
theorem totient_ratio_le_1001_div_192 (q : ℕ) (hq : 0<q) (hmax : q≤300000) :
    (q:ℝ)/(q.totient:ℝ)≤(1001/192:ℝ) := by
  classical
  let F : Finset ℕ := {2,3,5,7,11}
  let P := q.primeFactors
  have hpos (p : ℕ) (hp : p.Prime) : 0≤finiteTotientNormalizedFactor p := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
    have hp1 : 0≤(p:ℝ)-1 := by linarith
    unfold finiteTotientNormalizedFactor
    positivity
  have hsmall (p : ℕ) (hp : p∈F) : 1≤finiteTotientNormalizedFactor p := by
    simp only [F,mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> norm_num [finiteTotientNormalizedFactor]
  have hbig (p : ℕ) (hp : p∈P) (hn : p∉F) : finiteTotientNormalizedFactor p≤1 := by
    apply finiteTotientNormalizedFactor_large
    have hprime := Nat.prime_of_mem_primeFactors hp
    by_contra hh
    have hlt : p<13 := by omega
    interval_cases p <;> norm_num [F] at *
  have hprod : (∏ p∈P,finiteTotientNormalizedFactor p)≤(∏ p∈F,finiteTotientNormalizedFactor p) := by
    calc
      _ ≤ ∏ p∈P,if p∈F then finiteTotientNormalizedFactor p else 1 := by
        apply prod_le_prod (fun p hp=>hpos p (Nat.prime_of_mem_primeFactors hp))
        intro p hp
        split_ifs with h
        · exact le_rfl
        · exact hbig p hp h
      _ = ∏ p∈P.filter (fun p=>p∈F),finiteTotientNormalizedFactor p := (prod_filter _ _).symm
      _ ≤ ∏ p∈F,finiteTotientNormalizedFactor p :=
        prod_le_prod_of_subset_of_one_le (fun p hp=>(mem_filter.mp hp).2)
          (fun p hp=>le_trans (by norm_num) (hsmall p (mem_filter.mp hp).2)) (fun p hp hn=>hsmall p hp)
  have hcard : P.card≤6 := primeFactors_card_le_six_finite q hq hmax
  have heq : (∏ p∈P,(p:ℝ)/((p:ℝ)-1))=
      (13/12:ℝ)^P.card*(∏ p∈P,finiteTotientNormalizedFactor p) := by
    rw [←prod_const,←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    unfold finiteTotientNormalizedFactor
    ring
  rw [SieveModulusFactors.totient_ratio_prod q hq,heq]
  calc
    _ ≤ (13/12:ℝ)^6*(∏ p∈F,finiteTotientNormalizedFactor p) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard) hprod
        (prod_nonneg fun p hp=>hpos p (Nat.prime_of_mem_primeFactors hp)) (by positivity)
    _ = _ := by norm_num [F,finiteTotientNormalizedFactor]









end Helfgott



theorem solution (q : ℕ) (hq : 0<q) (hmax : q≤300000) :
    (q:ℝ)/(q.totient:ℝ)≤(1001/192:ℝ) := by
  apply Helfgott.totient_ratio_le_1001_div_192 <;> assumption
