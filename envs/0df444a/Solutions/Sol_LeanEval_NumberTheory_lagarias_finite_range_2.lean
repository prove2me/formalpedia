-- Prove2me | solution 2 for LeanEval.NumberTheory.lagarias_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T08:37:02.795147+00:00
-- url     : https://prove2.me/submissions/03927e2a-0d5f-4a08-9589-c496d41448fb

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LagariasFiniteProof

def expLower (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 20, q ^ i / (Nat.factorial i : ℝ)

def logLower (q : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range 8,
    ((q-1)/(q+1)) ^ (2*i+1) / (2*i+1 : ℝ)

lemma rhs_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    x + Real.exp x * Real.log x ≤ y + Real.exp y * Real.log y := by
  apply add_le_add hxy
  exact mul_le_mul (Real.exp_le_exp.mpr hxy)
    (Real.log_le_log (by linarith) hxy) (Real.log_nonneg hx) (Real.exp_nonneg y)

lemma lower_le {q : ℝ} (hq : 1 ≤ q) :
    q + expLower q * logLower q ≤ q + Real.exp q * Real.log q := by
  have hp : 0 < q+1 := by linarith
  have ht₀ : 0 ≤ (q-1)/(q+1) := div_nonneg (by linarith) hp.le
  have ht₁ : (q-1)/(q+1) < 1 := (div_lt_one hp).mpr (by linarith)
  have hid : (1+(q-1)/(q+1))/(1-(q-1)/(q+1)) = q := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div ht₀ ht₁ 8
  rw [hid] at hl
  have hl' : logLower q ≤ Real.log q := by unfold logLower; linarith
  have hl₀ : 0 ≤ logLower q := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg ht₀ _) (by positivity)
  have he : expLower q ≤ Real.exp q := Real.sum_le_exp_of_nonneg (by linarith) 20
  exact add_le_add le_rfl (mul_le_mul he hl' hl₀ (Real.exp_nonneg q))

def floorH (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 1000000 / (i+1)

lemma floorH_le (n : ℕ) :
    (floorH n : ℝ) / 1000000 ≤ (harmonic n : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range n, ((1000000 / (i+1) : ℕ) : ℝ) / 1000000 := by
      simp [floorH,Finset.sum_div]
    _ ≤ ∑ i ∈ Finset.range n, (((i+1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      have h : ((1000000 / (i+1) : ℕ) : ℝ) ≤ (1000000 : ℝ) / (i+1 : ℕ) :=
        Nat.cast_div_le
      calc
        _ ≤ ((1000000 : ℝ) / (i+1 : ℕ)) / 1000000 :=
          div_le_div_of_nonneg_right h (by norm_num)
        _ = _ := by push_cast; field_simp
    _ = (harmonic n : ℝ) := by simp [harmonic]

lemma harmonic_mono {n m : ℕ} (h : n ≤ m) :
    (harmonic n : ℝ) ≤ (harmonic m : ℝ) := by
  unfold harmonic
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun i _ _ => inv_nonneg.mpr (by positivity))



set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped ArithmeticFunction.sigma

private def checkpoints : List (ℕ × ℕ × ℕ × ℕ) := [
  (2,3,3,150),
  (3,4,4,183),
  (4,6,7,208),
  (6,8,12,244),
  (8,10,15,271),
  (10,12,18,292),
  (12,16,28,310),
  (16,18,31,338),
  (18,20,39,349),
  (20,24,42,359),
  (24,30,60,377),
  (30,36,72,399),
  (36,42,91,417),
  (42,48,96,432),
  (48,60,124,445),
  (60,72,168,467),
  (72,84,195,486),
  (84,90,224,501),
  (90,96,234,508),
  (96,108,252,514),
  (108,120,280,526),
  (120,144,360,536),
  (144,168,403,555),
  (168,180,480,570),
  (180,210,546,577),
  (210,216,576,592),
  (216,240,600,595),
  (240,288,744,605),
  (288,300,819,624),
  (300,336,868,628),
  (336,360,992,639),
  (360,420,1170,646),
  (420,480,1344,661),
  (480,504,1512,675),
  (504,540,1560,680),
  (540,600,1680,686),
  (600,630,1860,697),
  (630,660,1872,702),
  (660,720,2016,706),
  (720,840,2418,715),
  (840,960,2880,731),
  (960,1008,3048,744),
  (1008,1080,3224,749),
  (1080,1200,3600,756),
  (1200,1260,3844,766),
  (1260,1440,4368,771),
  (1440,1560,4914,784),
  (1560,1620,5040,792),
  (1620,1680,5082,796),
  (1680,1800,5952,800),
  (1800,1920,6045,807),
  (1920,1980,6120,813),
  (1980,2100,6552,816),
  (2100,2160,6944,822),
  (2160,2340,7440,825),
  (2340,2400,7644,833),
  (2400,2520,7812,835),
  (2520,2880,9360,840),
  (2880,3024,9906,854),
  (3024,3120,9920,859),
  (3120,3240,10416,862),
  (3240,3360,10890,865),
  (3360,3600,12096,869),
  (3600,3780,12493,876),
  (3780,3960,13440,881),
  (3960,4200,14040,885),
  (4200,4320,14880,891),
  (4320,4620,15120,894),
  (4620,4680,16128,901),
  (4680,5040,16380,902),
  (5040,5041,19344,910)
]

private def fastSigma (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.primeFactorsList.count p + 1), p ^ i

private lemma sigma_eq_fast (n : ℕ) (hn : n ≠ 0) : σ 1 n = fastSigma n := by
  simpa [fastSigma] using
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn

private lemma select_record (n : ℕ) (hn : 2 ≤ n) (hb : n ≤ 5040) :
    ∃ r ∈ checkpoints, r.1 ≤ n ∧ n < r.2.1 := by
  simp only [checkpoints, List.mem_cons, List.not_mem_nil, or_false,
    or_and_right, exists_or, exists_eq_left]
  omega

private lemma intervals_checked :
    (checkpoints.all fun r =>
      (List.range' r.1 (r.2.1-r.1)).all fun n =>
        decide (fastSigma n ≤ r.2.2.1)) = true := by decide +kernel

-- Certificate checkpoint: audited after arithmetic reduction.
#print axioms intervals_checked

private lemma cover_cert (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ checkpoints)
    (n : ℕ) (hn : 0 < n) (ha : r.1 ≤ n) (hb : n < r.2.1) :
    σ 1 n ≤ r.2.2.1 := by
  have h := List.all_eq_true.mp intervals_checked r hr
  have hm : n ∈ List.range' r.1 (r.2.1-r.1) := by
    apply List.mem_range'.mpr
    exact ⟨n-r.1, by omega, by omega⟩
  have hc : fastSigma n ≤ r.2.2.1 := of_decide_eq_true (List.all_eq_true.mp h n hm)
  rwa [sigma_eq_fast n (by omega)]

private lemma floor_cert : ∀ r ∈ checkpoints,
    100 ≤ r.2.2.2 ∧ r.2.2.2 * 10000 ≤ floorH r.1 := by decide +kernel

#print axioms floor_cert

private lemma strict_cert : ∀ r ∈ checkpoints,
    (r.2.2.1 : ℝ) < (r.2.2.2 : ℝ)/100 +
      expLower ((r.2.2.2 : ℝ)/100) * logLower ((r.2.2.2 : ℝ)/100) := by
  intro r hr
  simp only [checkpoints,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [expLower,logLower,Finset.sum_range_succ]

#print axioms strict_cert

lemma strict_finite {n : ℕ} (hn : 2 ≤ n) (hbound : n ≤ 5040) :
    ((σ 1 n : ℕ) : ℝ) < (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  obtain ⟨r,hr,ha,hb⟩ := select_record n hn hbound
  have hs := cover_cert r hr n (by omega) ha hb
  obtain ⟨hq,hfloor⟩ := floor_cert r hr
  have hq₁ : 1 ≤ (r.2.2.2 : ℝ)/100 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    norm_num
    exact_mod_cast hq
  have hqH : (r.2.2.2 : ℝ)/100 ≤ (harmonic n : ℝ) := by
    have hf : (r.2.2.2 : ℝ) * 10000 ≤ (floorH r.1 : ℝ) := by exact_mod_cast hfloor
    have hqf : (r.2.2.2 : ℝ)/100 ≤ (floorH r.1 : ℝ)/1000000 := by linarith
    exact hqf.trans ((floorH_le _).trans (harmonic_mono ha))
  have hs' : ((σ 1 n : ℕ) : ℝ) ≤ (r.2.2.1 : ℝ) := by exact_mod_cast hs
  exact hs'.trans_lt ((strict_cert _ hr).trans_le
    ((lower_le hq₁).trans (rhs_mono hq₁ hqH)))

end LagariasFiniteProof

open scoped ArithmeticFunction.sigma

theorem solution (n : ℕ) (hn : 0 < n) (hbound : n ≤ 5040) :
    (((σ 1 n : ℕ) : ℝ) ≤ (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ∧
      ((((σ 1 n : ℕ) : ℝ) = (harmonic n : ℝ) +
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)) ↔ n = 1) := by
  by_cases h : n = 1
  · subst n
    norm_num [harmonic_succ]
  · have hs := LagariasFiniteProof.strict_finite (by omega : 2 ≤ n) hbound
    exact ⟨hs.le,by simp [hs.ne,h]⟩

#print axioms solution
