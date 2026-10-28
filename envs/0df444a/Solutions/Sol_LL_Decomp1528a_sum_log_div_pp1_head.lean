-- Prove2me | solution 1 for LL_Decomp1528a.sum_log_div_pp1_head
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:53:28.76559+00:00
-- url     : https://prove2.me/submissions/36b8d9b5-b8b4-4527-8cfc-23282c049acf

import Mathlib

open Real Finset Chebyshev

namespace S218MH

def L2 : ℚ := 6931471808 / 10^10
def L3 : ℚ := 109861228877 / 10^11

lemma log2_le : Real.log 2 ≤ ((L2 : ℚ) : ℝ) := by
  have := Real.log_two_lt_d9; unfold L2; push_cast; norm_num at this ⊢; linarith

lemma log3_le : Real.log 3 ≤ ((L3 : ℚ) : ℝ) := by
  have := (abs_sub_le_iff.1 Real.log_three_near_10).1; unfold L3; push_cast; norm_num at this ⊢; linarith

lemma log_one_add_le {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ t - t^2/2 + t^3/3 := by
  let g : ℝ → ℝ := fun t => t - t^2/2 + t^3/3 - Real.log (1 + t)
  have hd : ∀ s, 0 ≤ s → HasDerivAt g (1 - s + s^2 - 1/(1+s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 s := by simpa using (hasDerivAt_id s).const_add 1
    have h2 := h1.log (by linarith)
    have h3 : HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3) (1 - s + s^2) s := by
      have := (((hasDerivAt_id' s).sub ((hasDerivAt_pow 2 s).div_const 2)).add
        ((hasDerivAt_pow 3 s).div_const 3))
      exact this.congr_deriv (by norm_num)
    exact (h3.sub h2).congr_deriv (by ring)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Ici] at hs; exact (hd s (le_of_lt hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs' : (0:ℝ) < s := hs
      rw [(hd s hs'.le).deriv]
      have : 1 - s + s^2 - 1/(1+s) = s^3/(1+s) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simp [g] at this
  linarith

def B (p a b : ℕ) : ℚ :=
  let t : ℚ := (p : ℚ) / (2^a * 3^b) - 1
  a * L2 + b * L3 + (t - t^2/2 + t^3/3)

lemma log_le_B (p a b : ℕ) (h : 2^a * 3^b ≤ p) : Real.log p ≤ ((B p a b : ℚ) : ℝ) := by
  have hm : (0:ℝ) < 2^a * 3^b := by positivity
  have hmp : (2:ℝ)^a * 3^b ≤ p := by exact_mod_cast h
  set t : ℝ := (p : ℝ) / (2^a * 3^b) - 1 with ht
  have ht0 : 0 ≤ t := by rw [ht, sub_nonneg, le_div_iff₀ hm]; linarith
  have hp : (p : ℝ) = (2^a * 3^b) * (1 + t) := by rw [ht]; field_simp; ring
  have hlog : Real.log p = a * Real.log 2 + b * Real.log 3 + Real.log (1 + t) := by
    rw [hp, Real.log_mul hm.ne' (by linarith), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  rw [hlog]
  have e : ((B p a b : ℚ) : ℝ) = a * ((L2:ℚ):ℝ) + b * ((L3:ℚ):ℝ) + (t - t^2/2 + t^3/3) := by
    simp only [B, ht]; push_cast; ring
  rw [e]
  have := log_one_add_le ht0
  have h2 := log2_le; have h3 := log3_le
  have : (a:ℝ) * Real.log 2 ≤ a * ((L2:ℚ):ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have : (b:ℝ) * Real.log 3 ≤ b * ((L3:ℚ):ℝ) := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

def best (p : ℕ) : ℕ × ℕ :=
  (List.range 11).foldl (fun acc a => (List.range 7).foldl (fun acc b =>
    if 2^a*3^b ≤ p ∧ 2^acc.1*3^acc.2 < 2^a*3^b then (a,b) else acc) acc) (0,0)

def T (p : ℕ) : ℕ :=
  if 2^(best p).1 * 3^(best p).2 ≤ p then
    (⌈B p (best p).1 (best p).2 * 10^12 / (p * (p - 1))⌉).toNat
  else 10^15

lemma term_le (p : ℕ) (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ (T p : ℝ) / 10^12 := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0:ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  rw [div_le_div_iff₀ hden (by norm_num)]
  unfold T
  split_ifs with h
  · have h1 := log_le_B p _ _ h
    set q : ℚ := B p (best p).1 (best p).2 * 10^12 / (p * (p - 1)) with hq
    have hc : q ≤ ((⌈q⌉.toNat : ℕ) : ℚ) := by
      have := Int.le_ceil q
      have h2 : (⌈q⌉ : ℚ) ≤ ((⌈q⌉.toNat : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
      push_cast at h2 ⊢; linarith
    have hc' : (q : ℝ) ≤ ((⌈q⌉.toNat : ℕ) : ℝ) := by exact_mod_cast hc
    have hqr : (q : ℝ) = ((B p (best p).1 (best p).2 : ℚ) : ℝ) * 10^12 / (p * (p - 1)) := by
      rw [hq]; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [hqr, div_le_iff₀ hden] at hc'
    nlinarith
  · have : Real.log p ≤ p := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    push_cast
    nlinarith

def isP (n : ℕ) : Bool := 2 ≤ n && (List.range 32).all (fun d => d < 2 || n ≤ d || n % d != 0)

lemma isP_of_prime {n : ℕ} (h : n.Prime) : isP n = true := by
  simp only [isP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨h.two_le, fun d _ => ?_⟩
  by_cases h1 : d < 2
  · simp [h1]
  by_cases h2 : n ≤ d
  · simp [h2]
  right; intro hmod
  have := (Nat.prime_def.1 h).2 d (Nat.dvd_of_mod_eq_zero hmod)
  omega

lemma check : ∑ n ∈ (range 1001).filter (fun n => isP n = true), T n ≤ 754500000000 := by
  decide +kernel

end S218MH

open S218MH in
theorem solution :
    ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 0.7545 := by
  have hsub : Nat.primesLE 1000 ⊆ (range 1001).filter (fun n => isP n = true) := by
    intro p hp
    simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
    simp only [mem_filter, mem_range]
    exact ⟨hp.1, isP_of_prime hp.2⟩
  calc ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ p ∈ Nat.primesLE 1000, (T p : ℝ) / 10^12 := by
        apply sum_le_sum; intro p hp
        simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
        exact term_le p hp.2.two_le
    _ ≤ ∑ p ∈ (range 1001).filter (fun n => isP n = true), (T p : ℝ) / 10^12 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ((∑ p ∈ (range 1001).filter (fun n => isP n = true), T p : ℕ) : ℝ) / 10^12 := by
        rw [Nat.cast_sum, sum_div]
    _ ≤ (754500000000 : ℝ) / 10^12 := by
        gcongr; exact_mod_cast check
    _ = 0.7545 := by norm_num
