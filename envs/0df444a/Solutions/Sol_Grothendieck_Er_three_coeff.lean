-- Prove2me | solution 1 for Grothendieck.Er_three_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:39:48.41406+00:00
-- url     : https://prove2.me/submissions/55a54968-ca07-424e-9e6a-f383e1f4a80d

import Mathlib
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators Real Topology
open Filter
namespace Grothendieck

/-! ## 0. elementary facts about `risingFact` -/

lemma risingFact_succ' (a : ℝ) (k : ℕ) :
    risingFact a (k + 1) = risingFact a k * (a + (k : ℝ)) := by
  simp [risingFact, Finset.prod_range_succ]

lemma risingFact_three_half (k : ℕ) :
    risingFact (1 / 2 + 1) k = (2 * (k : ℝ) + 1) * risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
      rw [risingFact_succ', ih, risingFact_succ']
      push_cast
      ring

lemma risingFact_half_pos (k : ℕ) : 0 < risingFact (1 / 2) k := by
  induction k with
  | zero => simp [risingFact]
  | succ n ih =>
      rw [risingFact_succ']
      have : (0:ℝ) < 1 / 2 + (n:ℝ) := by positivity
      positivity

/-! ## 1. The sequence `b k = (1/2)_k / k!` -/

/-- `b k = (1/2)_k / k!`. -/
def bc (k : ℕ) : ℝ := risingFact (1 / 2) k / (k.factorial : ℝ)

lemma bc_zero : bc 0 = 1 := by simp [bc, risingFact]

lemma bc_pos (k : ℕ) : 0 < bc k := by
  unfold bc
  have h1 : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have h2 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  exact div_pos h1 h2

/-- the recurrence `(k+1) b_{k+1} = (k+1/2) b_k`. -/
lemma bc_succ (k : ℕ) : ((k:ℝ) + 1) * bc (k+1) = ((k:ℝ) + 1/2) * bc k := by
  unfold bc
  rw [risingFact_succ', Nat.factorial_succ]
  push_cast
  have hpos : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hk0 : ((k:ℝ) + 1) ≠ 0 := ne_of_gt hk
  have hfk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact ne_of_gt this
  field_simp
  ring

/-- `b k` is the product `∏_{i<k} (i+1/2)/(i+1)`, hence `≤ 1`. -/
lemma bc_succ_div (k : ℕ) : bc (k+1) = bc k * (((k:ℝ) + 1/2) / ((k:ℝ) + 1)) := by
  have h := bc_succ k
  have hk : ((k:ℝ) + 1) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

lemma bc_le_one : ∀ k : ℕ, bc k ≤ 1 := by
  intro k
  induction k with
  | zero => simp [bc_zero]
  | succ n ih =>
      rw [bc_succ_div]
      have hle : (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have hnn : 0 ≤ (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) := by positivity
      nlinarith [bc_pos n]

lemma bc_nonneg (k : ℕ) : 0 ≤ bc k := le_of_lt (bc_pos k)

/-- The key bound `(2k+1) b_k²  ≤ 1` (Wallis). -/
lemma bc_sq_bound : ∀ k : ℕ, (2*(k:ℝ)+1) * (bc k)^2 ≤ 1 := by
  intro k
  induction k with
  | zero => simp [bc_zero]
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hkey : bc (n+1) = bc n * (((n:ℝ) + 1/2) / ((n:ℝ) + 1)) := bc_succ_div n
      have hratio : (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 ≤ (2*(n:ℝ)+1) * ((n:ℝ) + 1)^2 := by
        nlinarith
      have hbn : (0:ℝ) ≤ (bc n)^2 := sq_nonneg _
      have h2 : (0:ℝ) < ((n:ℝ) + 1)^2 := by positivity
      have hmul : (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 * (bc n)^2
          ≤ (2*(n:ℝ)+1) * (bc n)^2 * ((n:ℝ) + 1)^2 := by
        have h := mul_le_mul_of_nonneg_right hratio hbn
        calc (2*(n:ℝ)+3) * ((n:ℝ) + 1/2)^2 * (bc n)^2
            ≤ ((2*(n:ℝ)+1) * ((n:ℝ) + 1)^2) * (bc n)^2 := h
          _ = (2*(n:ℝ)+1) * (bc n)^2 * ((n:ℝ) + 1)^2 := by ring
      have hid : (2*(n:ℝ)+3) * (bc (n+1))^2 * ((n:ℝ)+1)^2
          = (2*(n:ℝ)+3) * ((n:ℝ)+1/2)^2 * (bc n)^2 := by
        rw [hkey]
        field_simp
      have hstep : (2*(n:ℝ)+3) * (bc (n+1))^2 ≤ (2*(n:ℝ)+1) * (bc n)^2 := by
        have h := hmul
        rw [← hid] at h
        exact le_of_mul_le_mul_right h h2
      have hgoal : (2*((n:ℝ)+1)+1) * bc (n+1)^2 ≤ 1 := by
        rw [show (2*((n:ℝ)+1)+1) = 2*(n:ℝ)+3 by ring]
        linarith
      push_cast
      exact hgoal

/-! ## 2. Summability of the binomial series and of its derivative -/

lemma summable_abs_pow_sub_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (n:ℝ) * r^(n-1)) := by
  have hr1' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
  have hid : (fun n : ℕ => (n:ℝ) * r^(n-1)) = fun n : ℕ => ((n:ℝ) * r^n) / r := by
    funext n
    rcases n with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      field_simp
  rw [hid]
  simpa using (summable_pow_mul_geometric_of_norm_lt_one 1 hr1').div_const r

lemma summable_abs_pow_sub_one' {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (n:ℝ) * |x|^(n-1)) := by
  rcases eq_or_lt_of_le (abs_nonneg x) with h | h
  · rw [← h]
    refine summable_of_ne_finset_zero (s := ({0, 1} : Finset ℕ)) ?_
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    obtain ⟨h1, h0⟩ := hn
    have hne : n - 1 ≠ 0 := by omega
    rw [zero_pow hne]
    ring
  · exact summable_abs_pow_sub_one h hx

lemma summable_bc_mul_pow {x : ℝ} (hx : |x| < 1) : Summable (fun k : ℕ => bc k * x^k) := by
  have hg : Summable (fun k : ℕ => ‖x‖^k) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
  refine Summable.of_norm_bounded hg (fun k => ?_)
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (bc_pos k)]
  have h1 : bc k ≤ 1 := bc_le_one k
  have h0 : (0:ℝ) ≤ ‖x‖^k := by positivity
  nlinarith

lemma summable_bc_mul_pow_shift {x : ℝ} (hx : |x| < 1) :
    Summable (fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) := by
  refine Summable.of_norm_bounded (summable_abs_pow_sub_one' hx) (fun n => ?_)
  have hstep : ‖(n:ℝ) * bc n * x^(n-1)‖ = (n:ℝ) * bc n * |x|^(n-1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
        abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hstep]
  have h1 : bc n ≤ 1 := bc_le_one n
  have hy : (0:ℝ) ≤ |x|^(n-1) := by positivity
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h2 : (n:ℝ) * bc n * |x|^(n-1) ≤ (n:ℝ) * 1 * |x|^(n-1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) hy
  linarith

/-! ## 3. The binomial series `B(x) = ∑ b_k x^k = (1-x)^{-1/2}` -/

/-- the binomial series. -/
def Bfun (x : ℝ) : ℝ := ∑' k : ℕ, bc k * x^k

/-- its formal derivative. -/
def Afun (x : ℝ) : ℝ := ∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^k

lemma Bfun_zero : Bfun 0 = 1 := by
  rw [Bfun, tsum_eq_single 0]
  · simp [bc_zero]
  · intro b hb
    simp [hb]

lemma summable_Afun {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => ((k:ℝ)+1) * bc (k+1) * x^k) := by
  have hs : Summable (fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) := summable_bc_mul_pow_shift hx
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ) * bc n * x^(n-1)) 1).mpr hs
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using hshift

lemma tsum_deriv_shift {x : ℝ} (hx : |x| < 1) :
    (∑' n : ℕ, (n:ℝ) * bc n * x^(n-1)) = Afun x := by
  have hs := summable_bc_mul_pow_shift hx
  have h := Summable.tsum_eq_zero_add hs
  simp only [Nat.cast_zero, zero_mul, Nat.zero_sub, pow_zero, mul_one, zero_add,
    Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at h
  rw [Afun, ← h]

/-- the derivative of the binomial series. -/
lemma hasDerivAt_Bfun {x : ℝ} (hx : |x| < 1) : HasDerivAt Bfun (Afun x) x := by
  obtain ⟨r, hrx, hr1⟩ : ∃ r : ℝ, |x| < r ∧ r < 1 := ⟨(|x| + 1)/2, by linarith, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hrx
  have hmem : x ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hu : Summable (fun n : ℕ => (n:ℝ) * r^(n-1)) := summable_abs_pow_sub_one hr0 hr1
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun y : ℝ => bc n * y^n) ((n:ℝ) * bc n * y^(n-1)) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y^n) ((n:ℝ) * y^(n-1)) y := hasDerivAt_pow n y
    have h2 := h1.const_mul (bc n)
    have he : bc n * ((n:ℝ) * y^(n-1)) = (n:ℝ) * bc n * y^(n-1) := by ring
    rw [he] at h2
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      ‖(n:ℝ) * bc n * y^(n-1)‖ ≤ (n:ℝ) * r^(n-1) := by
    intro n y hy
    have hy' : |y| ≤ r := by
      rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp
    · have hstep : ‖(n:ℝ) * bc n * y^(n-1)‖ = (n:ℝ) * bc n * |y|^(n-1) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
          abs_of_nonneg (Nat.cast_nonneg n)]
      rw [hstep]
      have hpow : |y|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg y) hy' _
      have h1 : bc n ≤ 1 := bc_le_one n
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have h3 : (0:ℝ) ≤ |y|^(n-1) := by positivity
      have hb1 : (n:ℝ) * bc n * |y|^(n-1) ≤ (n:ℝ) * 1 * |y|^(n-1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) h3
      have hb2 : (n:ℝ) * 1 * |y|^(n-1) ≤ (n:ℝ) * 1 * r^(n-1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ (n:ℝ) * 1)
      calc (n:ℝ) * bc n * |y|^(n-1) ≤ (n:ℝ) * 1 * |y|^(n-1) := hb1
        _ ≤ (n:ℝ) * 1 * r^(n-1) := hb2
        _ = (n:ℝ) * r^(n-1) := by ring
  have hpt : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hsum0 : Summable (fun n : ℕ => bc n * (0:ℝ)^n) := by
    refine summable_of_ne_finset_zero (s := ({0} : Finset ℕ)) ?_
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (y₀ := (0:ℝ))
    (u := fun n : ℕ => (n:ℝ) * r^(n-1))
    (g := fun (n:ℕ) (y:ℝ) => bc n * y^n)
    (g' := fun (n:ℕ) (y:ℝ) => (n:ℝ) * bc n * y^(n-1))
    (t := Set.Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound hpt hsum0 hmem
  rw [← tsum_deriv_shift hx]
  exact hmain

lemma bc_recur (k : ℕ) : ((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k = (1/2) * bc k := by
  have h := bc_succ k
  linarith

lemma summable_k_bc_pow {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ => (k:ℝ) * bc k * x^k) := by
  have hg : Summable (fun k : ℕ => (k:ℝ) * |x|^k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1
      (r := |x|) (by simpa only [Real.norm_eq_abs, abs_abs] using hx)
    simpa using h
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hstep : ‖(n:ℝ) * bc n * x^n‖ = (n:ℝ) * bc n * |x|^n := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (bc_pos n),
      abs_of_nonneg (Nat.cast_nonneg n)]
  rw [hstep]
  have h1 : bc n ≤ 1 := bc_le_one n
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h3 : (0:ℝ) ≤ |x|^n := by positivity
  have hb1 : (n:ℝ) * bc n * |x|^n ≤ (n:ℝ) * 1 * |x|^n :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hn) h3
  calc (n:ℝ) * bc n * |x|^n ≤ (n:ℝ) * 1 * |x|^n := hb1
    _ = (n:ℝ) * |x|^n := by ring

/-- the ODE satisfied by the binomial series: `(1-x) B'(x) = B(x)/2`. -/
lemma Bfun_ode {x : ℝ} (hx : |x| < 1) : (1 - x) * Afun x = (1/2) * Bfun x := by
  have hA : Summable (fun k : ℕ => ((k:ℝ)+1) * bc (k+1) * x^k) := summable_Afun hx
  have hB : Summable (fun k : ℕ => bc k * x^k) := summable_bc_mul_pow hx
  have hk : Summable (fun k : ℕ => (k:ℝ) * bc k * x^k) := summable_k_bc_pow hx
  have hxA : x * Afun x = ∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^(k+1) := by
    rw [Afun, ← Summable.tsum_mul_left x hA]
    exact tsum_congr (fun k => by ring)
  have hshift : (∑' k : ℕ, ((k:ℝ)+1) * bc (k+1) * x^(k+1))
      = ∑' k : ℕ, (k:ℝ) * bc k * x^k := by
    have h := Summable.tsum_eq_zero_add hk
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    refine Eq.trans ?_ h.symm
    refine tsum_congr (fun k => ?_)
    push_cast
    ring
  have hsub : Afun x - x * Afun x
      = ∑' k : ℕ, (((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k) * x^k := by
    rw [hxA, Afun, hshift, ← Summable.tsum_sub hA hk]
    exact tsum_congr (fun k => by ring)
  have hhalf : (∑' k : ℕ, (((k:ℝ)+1) * bc (k+1) - (k:ℝ) * bc k) * x^k)
      = (1/2) * Bfun x := by
    rw [Bfun, ← Summable.tsum_mul_left (1/2) hB]
    exact tsum_congr (fun k => by rw [bc_recur k]; ring)
  rw [← hhalf, ← hsub]
  ring

/-- `Q(x) = (1-x)^{-1/2}`. -/
def Qfun (x : ℝ) : ℝ := (1 - x) ^ (-(1/2) : ℝ)

lemma hasDerivAt_Qfun {x : ℝ} (hx : x < 1) :
    HasDerivAt Qfun ((1/2) * (1-x)^(-(3/2) : ℝ)) x := by
  have hf : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1:ℝ)
  have hg : HasDerivAt (fun _ : ℝ => (-(1/2) : ℝ)) 0 x := hasDerivAt_const x _
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h := hf.rpow hg hpos
  have hsimp : (-1 : ℝ) * (-(1/2)) * (1-x)^((-(1/2) : ℝ) - 1) + 0 * (1-x)^(-(1/2):ℝ) * Real.log (1-x)
      = (1/2) * (1-x)^(-(3/2) : ℝ) := by
    rw [show (-(1/2) : ℝ) - 1 = -(3/2) by ring]
    ring
  rw [hsimp] at h
  exact h

lemma Qfun_ode {x : ℝ} (hx : x < 1) :
    (1 - x) * ((1/2) * (1-x)^(-(3/2) : ℝ)) = (1/2) * Qfun x := by
  unfold Qfun
  have hpos : (0:ℝ) < 1 - x := by linarith
  have h := Real.rpow_add hpos (1:ℝ) (-(3/2) : ℝ)
  rw [show (1:ℝ) + (-(3/2)) = -(1/2) by ring, Real.rpow_one] at h
  rw [h]
  ring

/-- If a function differentiable on `(-1,1)` has derivative zero there and vanishes at `0`,
then it vanishes identically. -/
lemma eq_zero_of_hasDerivAt_zero {f : ℝ → ℝ}
    (h : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt f 0 y) (h0 : f 0 = 0) :
    ∀ x ∈ Set.Ioo (-1:ℝ) 1, f x = 0 := by
  intro x hx
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hlt
      (fun y hy => ((h y ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩).continuousAt).continuousWithinAt)
      (fun y hy => (h y ⟨by linarith [hy.1, hx.1], by linarith [hy.2]⟩).differentiableAt.differentiableWithinAt)
    have hc' : c ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith [hc.1, hx.1], by linarith [hc.2]⟩
    rw [(h c hc').deriv] at hcd
    have hne : (0:ℝ) - x ≠ 0 := by linarith
    field_simp at hcd
    linarith [hcd]
  · rw [heq]; exact h0
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hgt
      (fun y hy => ((h y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩).continuousAt).continuousWithinAt)
      (fun y hy => (h y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩).differentiableAt.differentiableWithinAt)
    have hc' : c ∈ Set.Ioo (-1:ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2, hx.2]⟩
    rw [(h c hc').deriv] at hcd
    have hne : x - 0 ≠ 0 := by linarith
    field_simp at hcd
    linarith [hcd]

/-- `∑ b_k x^k = (1-x)^{-1/2}` on `(-1,1)`. -/
theorem Bfun_eq {x : ℝ} (hx : |x| < 1) : Bfun x = (1 - x) ^ (-(1/2) : ℝ) := by
  obtain ⟨hx1, hx2⟩ := abs_lt.mp hx
  set D : ℝ → ℝ := fun y => Bfun y - Qfun y with hD
  have hDderiv : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt D (D y / (2*(1-y))) y := by
    intro y hy
    have hy1 : y < 1 := hy.2
    have habs : |y| < 1 := by rw [abs_lt]; exact hy
    have h1 : HasDerivAt Bfun (Afun y) y := hasDerivAt_Bfun habs
    have h2 : HasDerivAt Qfun ((1/2)*(1-y)^(-(3/2) : ℝ)) y := hasDerivAt_Qfun hy1
    have hB := Bfun_ode habs
    have hQ := Qfun_ode hy1
    have hne : (1:ℝ) - y ≠ 0 := by linarith
    have hval : Afun y - (1/2)*(1-y)^(-(3/2) : ℝ) = (Bfun y - Qfun y)/(2*(1-y)) := by
      field_simp
      linarith [hB, hQ]
    have h3 : HasDerivAt (fun z => Bfun z - Qfun z) ((Bfun y - Qfun y)/(2*(1-y))) y := by
      have h1' : HasDerivAt (fun z => Bfun z - Qfun z)
          (Afun y - (1/2)*(1-y)^(-(3/2) : ℝ)) y := h1.sub h2
      rw [hval] at h1'
      exact h1'
    rw [hD]
    exact h3
  have hE : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt (fun z => (D z)^2 * (1-z)) 0 y := by
    intro y hy
    have h1 : HasDerivAt D (D y / (2*(1-y))) y := hDderiv y hy
    have h2 : HasDerivAt (fun z => D z * D z)
        ((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) y := h1.mul h1
    have h3 : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1:ℝ)
    have h4 : HasDerivAt (fun z => (D z * D z) * (1-z))
        (((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) * (1-y) + (D y * D y) * (-1)) y :=
      h2.mul h3
    have hne : (1:ℝ) - y ≠ 0 := by linarith [hy.2]
    have hzero : ((D y/(2*(1-y))) * D y + D y * (D y/(2*(1-y)))) * (1-y) + (D y * D y) * (-1) = 0 := by
      field_simp
      ring
    rw [hzero] at h4
    convert h4 using 1
    ring_nf
  have hone := eq_zero_of_hasDerivAt_zero hE (by simp [D, Bfun_zero, Qfun])
  have hdx : D x = 0 := by
    have hz := hone x ⟨hx1, hx2⟩
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hsq : (D x)^2 = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd h (ne_of_gt h1x)
    by_contra hne0
    have hpos : (0:ℝ) < (D x)^2 := by positivity
    linarith
  rw [hD] at hdx
  simpa [Qfun, sub_eq_zero] using hdx

/-! ## 4. The arcsine series `∑_k (b_k/(2k+1)) t^{2k+1} = arcsin t` -/

/-- the arcsine series. -/
def Ffun (t : ℝ) : ℝ := ∑' k : ℕ, bc k / (2*(k:ℝ)+1) * t^(2*k+1)

lemma Ffun_zero : Ffun 0 = 0 := by
  rw [Ffun]
  have h : (fun k : ℕ => bc k / (2*(k:ℝ)+1) * (0:ℝ)^(2*k+1)) = fun _ => 0 := by
    funext k
    have hz : (2*k+1) ≠ 0 := by omega
    rw [zero_pow hz]
    ring
  rw [h, tsum_zero]

lemma summable_Ffun {t : ℝ} (ht : |t| < 1) :
    Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1) * t^(2*k+1)) := by
  have hg : Summable (fun k : ℕ => |t|^k) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using ht)
  refine Summable.of_norm_bounded hg (fun n => ?_)
  have hd : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have hstep : ‖bc n / (2*(n:ℝ)+1) * t^(2*n+1)‖ = bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (bc_pos n), abs_of_pos hd, abs_pow]
  rw [hstep]
  have ht0 : |t| < 1 := ht
  have ht1 : |t| ^ (2*n+1) ≤ |t|^n := by
    have hnn : (0:ℝ) ≤ |t| := abs_nonneg t
    exact pow_le_pow_of_le_one hnn ht0.le (by omega)
  have hle : bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) ≤ 1 * |t|^n := by
    have hbc : bc n / (2*(n:ℝ)+1) ≤ 1 := by
      rw [div_le_one hd]
      have h1 : bc n ≤ 1 := bc_le_one n
      linarith
    have hnn : (0:ℝ) ≤ |t|^(2*n+1) := by positivity
    calc bc n / (2*(n:ℝ)+1) * |t|^(2*n+1) ≤ 1 * |t|^(2*n+1) :=
          mul_le_mul_of_nonneg_right hbc hnn
      _ ≤ 1 * |t|^n := mul_le_mul_of_nonneg_left ht1 zero_le_one
  simpa using hle

/-- `Ffun` has derivative `Bfun (t^2) = (1-t^2)^{-1/2}`. -/
lemma hasDerivAt_Ffun {t : ℝ} (ht : |t| < 1) : HasDerivAt Ffun (Bfun (t^2)) t := by
  obtain ⟨r, hrt, hr1⟩ : ∃ r : ℝ, |t| < r ∧ r < 1 := ⟨(|t| + 1)/2, by linarith, by linarith⟩
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg t) hrt
  have hmem : t ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  -- summable bound: r^{2n}
  have hr2 : r^2 < 1 := by nlinarith [hr0, hr1]
  have hu : Summable (fun n : ℕ => ((r^2)^n)) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r^2)]
    exact hr2
  have hderiv : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun y : ℝ => bc n / (2*(n:ℝ)+1) * y^(2*n+1)) (bc n * y^(2*n)) y := by
    intro n y _
    have h1 : HasDerivAt (fun y : ℝ => y^(2*n+1)) ((2*(n:ℝ)+1) * y^(2*n)) y := by
      have h := hasDerivAt_pow (2*n+1) y
      have he : ((2*n+1 : ℕ) : ℝ) = 2*(n:ℝ)+1 := by push_cast; ring
      rw [he] at h
      have hsub : 2*n+1-1 = 2*n := by omega
      rw [hsub] at h
      exact h
    have h2 := h1.const_mul (bc n / (2*(n:ℝ)+1))
    have hden : (2*(n:ℝ)+1) ≠ 0 := by positivity
    have heq : bc n / (2*(n:ℝ)+1) * ((2*(n:ℝ)+1) * y^(2*n)) = bc n * y^(2*n) := by
      field_simp
    rw [heq] at h2
    exact h2
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r → ‖bc n * y^(2*n)‖ ≤ (r^2)^n := by
    intro n y hy
    have hy' : |y| ≤ r := by rw [abs_le]; exact ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hstep : ‖bc n * y^(2*n)‖ = bc n * |y|^(2*n) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (bc_pos n), abs_pow]
    rw [hstep]
    have h1 : bc n ≤ 1 := bc_le_one n
    have hpow : |y|^(2*n) ≤ r^(2*n) := pow_le_pow_left₀ (abs_nonneg y) hy' _
    have hrw : r^(2*n) = (r^2)^n := by rw [← pow_mul]
    rw [hrw] at hpow
    calc bc n * |y|^(2*n) ≤ 1 * (r^2)^n := by
          apply mul_le_mul h1 hpow (by positivity) (by positivity)
      _ = (r^2)^n := by ring
  have hpt : (0:ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, by linarith⟩
  have hsum0 : Summable (fun n : ℕ => bc n / (2*(n:ℝ)+1) * (0:ℝ)^(2*n+1)) := by
    refine summable_of_ne_finset_zero (s := (∅ : Finset ℕ)) ?_
    intro n _
    have h : (2*n+1) ≠ 0 := by omega
    rw [zero_pow h]
    ring
  have hmain := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ) (y₀ := (0:ℝ))
    (u := fun n : ℕ => (r^2)^n)
    (g := fun (n:ℕ) (y:ℝ) => bc n / (2*(n:ℝ)+1) * y^(2*n+1))
    (g' := fun (n:ℕ) (y:ℝ) => bc n * y^(2*n))
    (t := Set.Ioo (-r) r) hu isOpen_Ioo isPreconnected_Ioo hderiv hbound hpt hsum0 hmem
  have hfin : (∑' n : ℕ, bc n * t^(2*n)) = Bfun (t^2) := by
    rw [Bfun]
    exact tsum_congr (fun n => by rw [pow_mul])
  rw [← hfin]
  exact hmain

/-- `arcsin` has derivative `(1-t²)^{-1/2}` on `(-1,1)`. -/
lemma hasDerivAt_arcsin' {t : ℝ} (ht : |t| < 1) :
    HasDerivAt Real.arcsin ((1 - t^2) ^ (-(1/2) : ℝ)) t := by
  have ht1 : t ≠ 1 := by
    intro h; rw [h] at ht; norm_num at ht
  have ht2 : t ≠ -1 := by
    intro h; rw [h] at ht; norm_num at ht
  have h := Real.hasDerivAt_arcsin ht2 ht1
  have hpos : (0:ℝ) < 1 - t^2 := by
    have := abs_lt.mp ht
    nlinarith [this.1, this.2]
  have heq : (1:ℝ) / √(1 - t^2) = (1 - t^2) ^ (-(1/2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hpos.le]
  rw [heq] at h
  exact h

/-- the arcsine series is `arcsin` on `(-1,1)`. -/
theorem Ffun_eq_arcsin {t : ℝ} (ht : |t| < 1) : Ffun t = Real.arcsin t := by
  have key : ∀ y ∈ Set.Ioo (-1:ℝ) 1, HasDerivAt (fun z => Ffun z - Real.arcsin z) 0 y := by
    intro y hy
    have hyabs : |y| < 1 := by rw [abs_lt]; exact hy
    have h1 : HasDerivAt Ffun (Bfun (y^2)) y := hasDerivAt_Ffun hyabs
    have h2 : HasDerivAt Real.arcsin ((1-y^2)^(-(1/2):ℝ)) y := hasDerivAt_arcsin' hyabs
    have hy2 : |y^2| < 1 := by
      rw [abs_lt]; constructor <;> nlinarith [hy.1, hy.2]
    have h3 : Bfun (y^2) = (1-y^2)^(-(1/2):ℝ) := Bfun_eq hy2
    have h4 : HasDerivAt (fun z => Ffun z - Real.arcsin z)
        (Bfun (y^2) - (1-y^2)^(-(1/2):ℝ)) y := h1.sub h2
    rw [h3, sub_self] at h4
    exact h4
  have h0 : (fun z => Ffun z - Real.arcsin z) 0 = 0 := by
    simp [Ffun_zero]
  have hfin := eq_zero_of_hasDerivAt_zero key h0 t (abs_lt.mp ht)
  simp only [sub_eq_zero] at hfin
  exact hfin

/-! ## 5. `Er 1 t = (2/π) arcsin t` -/

lemma Cr_one : Cr 1 = 2 / Real.pi := by
  unfold Cr
  norm_num
  rw [Real.Gamma_one_half_eq, Real.sq_sqrt Real.pi_pos.le, div_eq_mul_inv]

lemma ErCoeff_one (k : ℕ) : ErCoeff 1 k = Cr 1 * (bc k / (2*(k:ℝ)+1)) := by
  unfold ErCoeff bc
  simp only [Nat.cast_one]
  rw [risingFact_three_half]
  push_cast
  have hpos : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
    have : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    exact ne_of_gt this
  have h2k : (2*(k:ℝ)+1) ≠ 0 := by positivity
  field_simp

/-- **The `r = 1` case of the right-hand side of Lemma 2.1**: `E_1(t) = (2/π) arcsin t`. -/
theorem Er_one {t : ℝ} (ht : |t| < 1) : Er 1 t = 2 / Real.pi * Real.arcsin t := by
  have hsummable : Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1) * t^(2*k+1)) := summable_Ffun ht
  have hstep : (∑' k : ℕ, ErCoeff 1 k * t^(2*k+1)) = (2/Real.pi) * Ffun t := by
    rw [Ffun, ← Summable.tsum_mul_left (2/Real.pi) hsummable]
    exact tsum_congr (fun k => by rw [ErCoeff_one, Cr_one]; ring)
  rw [Er, hstep, Ffun_eq_arcsin ht]

/-! ## 6. The boundary points `t = ±1` -/

lemma bc_telescope (k : ℕ) : bc k - bc (k+1) = bc k / (2*((k:ℝ)+1)) := by
  have h := bc_succ k
  have hk : ((k:ℝ)+1) ≠ 0 := by positivity
  field_simp at h ⊢
  linarith

lemma bc_div_le (k : ℕ) : bc k / (2*(k:ℝ)+1) ≤ 2 * (bc k - bc (k+1)) := by
  rw [bc_telescope]
  have h1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have h3 : (0:ℝ) ≤ bc k := bc_nonneg k
  have h4 : (k:ℝ)+1 ≤ 2*(k:ℝ)+1 := by
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have h5 : bc k / (2*(k:ℝ)+1) ≤ bc k / ((k:ℝ)+1) :=
    div_le_div_of_nonneg_left h3 h1 h4
  have h6 : (2:ℝ) * (bc k / (2*((k:ℝ)+1))) = bc k / ((k:ℝ)+1) := by
    field_simp
  rw [h6]
  exact h5

lemma summable_bc_div : Summable (fun k : ℕ => bc k / (2*(k:ℝ)+1)) := by
  refine summable_of_sum_range_le (f := fun k : ℕ => bc k / (2*(k:ℝ)+1)) (c := 2)
    (fun n => ?_) (fun n => ?_)
  · have h1 : (0:ℝ) < bc n := bc_pos n
    have h2 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
    positivity
  · calc ∑ k ∈ Finset.range n, bc k / (2*(k:ℝ)+1)
        ≤ ∑ k ∈ Finset.range n, 2 * (bc k - bc (k+1)) :=
          Finset.sum_le_sum (fun k _ => bc_div_le k)
      _ = 2 * (bc 0 - bc n) := by
          rw [← Finset.mul_sum]
          have h := Finset.sum_range_sub (f := bc) n
          have h2 : ∑ i ∈ Finset.range n, (bc i - bc (i + 1))
              = -(∑ i ∈ Finset.range n, (bc (i + 1) - bc i)) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl (fun i _ => by ring)
          rw [h2, h]
          ring
      _ ≤ 2 := by
          have h1 : bc 0 = 1 := bc_zero
          have h2 : 0 < bc n := bc_pos n
          rw [h1]
          linarith

lemma ErCoeff_one_nonneg (n : ℕ) : 0 ≤ ErCoeff 1 n := by
  rw [ErCoeff_one]
  have h1 : (0:ℝ) < Cr 1 := by rw [Cr_one]; positivity
  have h2 : (0:ℝ) ≤ bc n / (2*(n:ℝ)+1) := by
    have h3 : (0:ℝ) < bc n := bc_pos n
    have h4 : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
    positivity
  positivity

lemma summable_ErCoeff_one : Summable (fun k : ℕ => ErCoeff 1 k) := by
  have h := summable_bc_div.mul_left (Cr 1)
  have h2 : (fun k : ℕ => Cr 1 * (bc k / (2*(k:ℝ)+1))) = fun k => ErCoeff 1 k := by
    funext k
    exact (ErCoeff_one k).symm
  rw [h2] at h
  exact h

lemma continuousOn_Er_one : ContinuousOn (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) := by
  have hu := summable_ErCoeff_one
  have hb : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1:ℝ) 1 →
      ‖ErCoeff 1 n * x^(2*n+1)‖ ≤ ErCoeff 1 n := by
    intro n x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hlt : |x|^(2*n+1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_one_nonneg n)]
    calc ErCoeff 1 n * |x|^(2*n+1) ≤ ErCoeff 1 n * 1 := by
          apply mul_le_mul_of_nonneg_left hlt (ErCoeff_one_nonneg n)
      _ = ErCoeff 1 n := by ring
  have hunif := tendstoUniformlyOn_tsum hu hb
  have hcont : ∀ (s : Finset ℕ), ContinuousOn
      (fun t : ℝ => ∑ k ∈ s, ErCoeff 1 k * t^(2*k+1)) (Set.Icc (-1:ℝ) 1) := by
    intro s
    have hc : Continuous (fun t : ℝ => ∑ k ∈ s, ErCoeff 1 k * t^(2*k+1)) := by
      apply continuous_finset_sum
      intro k _
      fun_prop
    exact hc.continuousOn
  exact hunif.continuousOn (Eventually.of_forall hcont).frequently

theorem Er_one_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Er 1 t = 2 / Real.pi * Real.arcsin t := by
  obtain ⟨ht1, ht2⟩ := ht
  have keym1 : Er 1 (-1) = 2 / Real.pi * Real.arcsin (-1) := by
    haveI : (𝓝[Set.Ioo (-1:ℝ) 1] (-1)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num⟩
    have hcontIcc : ContinuousWithinAt (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) (-1) :=
      continuousOn_Er_one.continuousWithinAt (by simp)
    have h2 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] (-1)) (𝓝 (Er 1 (-1))) :=
      hcontIcc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hg : ContinuousWithinAt (fun t => 2 / Real.pi * Real.arcsin t) (Set.Ioo (-1:ℝ) 1) (-1) :=
      (continuous_const.mul Real.continuous_arcsin).continuousWithinAt
    have h3 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] (-1))
        (𝓝 (2 / Real.pi * Real.arcsin (-1))) :=
      hg.congr' (eventually_of_mem self_mem_nhdsWithin
        (fun y hy => (Er_one (by rw [abs_lt]; exact hy)).symm))
    exact tendsto_nhds_unique h2 h3
  have key1 : Er 1 1 = 2 / Real.pi * Real.arcsin 1 := by
    haveI : (𝓝[Set.Ioo (-1:ℝ) 1] 1).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
      exact ⟨by norm_num, le_rfl⟩
    have hcontIcc : ContinuousWithinAt (fun t => Er 1 t) (Set.Icc (-1:ℝ) 1) 1 :=
      continuousOn_Er_one.continuousWithinAt (by simp)
    have h2 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] 1) (𝓝 (Er 1 1)) :=
      hcontIcc.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
    have hg : ContinuousWithinAt (fun t => 2 / Real.pi * Real.arcsin t) (Set.Ioo (-1:ℝ) 1) 1 :=
      (continuous_const.mul Real.continuous_arcsin).continuousWithinAt
    have h3 : Tendsto (fun t => Er 1 t) (𝓝[Set.Ioo (-1:ℝ) 1] 1)
        (𝓝 (2 / Real.pi * Real.arcsin 1)) :=
      hg.congr' (eventually_of_mem self_mem_nhdsWithin
        (fun y hy => (Er_one (by rw [abs_lt]; exact hy)).symm))
    exact tendsto_nhds_unique h2 h3
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · rcases lt_trichotomy t (-1) with h | h | h
    · linarith
    · rw [h]; exact keym1
    · exact Er_one (by rw [abs_lt]; exact ⟨h, hlt⟩)
  · rw [heq]; exact key1
  · linarith

/-! ## 7. General facts about `Cr`, `ErCoeff`, `Er` (for `r ≥ 1`) -/

lemma Cr_pos {r : ℕ} (hr : 1 ≤ r) : 0 < Cr r := by
  unfold Cr
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have h1 : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have h2 : (0:ℝ) < Real.Gamma ((r:ℝ)/2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have : (0:ℝ) < Real.Gamma (((r:ℝ)+1)/2) / Real.Gamma ((r:ℝ)/2) := div_pos h1 h2
  positivity

lemma risingFact_half_sq_pos (k : ℕ) : 0 < (risingFact (1/2) k)^2 := by
  have := risingFact_half_pos k
  positivity

lemma risingFact_arg_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < risingFact ((r:ℝ)/2+1) k := by
  unfold risingFact
  apply Finset.prod_pos
  intro i _
  have h1 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  have h2 : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  push_cast
  linarith

theorem ErCoeff_nonneg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 ≤ ErCoeff r k := by
  unfold ErCoeff
  have h1 : 0 < Cr r := Cr_pos hr
  have h2 : 0 < (risingFact (1/2) k)^2 := risingFact_half_sq_pos k
  have h3 : 0 < risingFact ((r:ℝ)/2+1) k := risingFact_arg_pos hr k
  have h4 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  positivity

theorem Er_zero (r : ℕ) : Er r 0 = 0 := by
  rw [Er]
  have h : (fun k : ℕ => ErCoeff r k * (0:ℝ)^(2*k+1)) = fun _ => 0 := by
    funext k
    have hz : (2*k+1) ≠ 0 := by omega
    rw [zero_pow hz]
    ring
  rw [h, tsum_zero]

/-- For `r = 1`, `E_1` maps `[-1,1]` into `[-1,1]`. -/
theorem abs_Er_one_le_one {t : ℝ} (ht : t ∈ Set.Icc (-1:ℝ) 1) : |Er 1 t| ≤ 1 := by
  rw [Er_one_Icc ht, abs_mul]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : |2 / Real.pi| = 2 / Real.pi := by
    rw [abs_of_pos]; positivity
  rw [h1]
  have h2 : |Real.arcsin t| ≤ Real.pi / 2 :=
    abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin t, Real.arcsin_le_pi_div_two t⟩
  calc 2 / Real.pi * |Real.arcsin t| ≤ 2 / Real.pi * (Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 := by field_simp

end Grothendieck

namespace Grothendieck

/-! ## 8. Summability, continuity and monotonicity of `Er r` for `r ≥ 1` -/

lemma risingFact_mono_arg {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    risingFact (1/2+1) k ≤ risingFact ((r:ℝ)/2+1) k := by
  unfold risingFact
  apply Finset.prod_le_prod
  · intro i _
    have h : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    linarith
  · intro i _
    have h : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith

lemma ErCoeff_le {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    ErCoeff r k ≤ Cr r * (bc k / (2*(k:ℝ)+1)) := by
  unfold ErCoeff
  have hC : 0 < Cr r := Cr_pos hr
  have hsq : 0 < (risingFact (1/2) k)^2 := risingFact_half_sq_pos k
  have hfk : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hden1 : 0 < risingFact (1/2+1) k := by
    unfold risingFact
    apply Finset.prod_pos
    intro i _
    have h : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    push_cast
    linarith
  have hden2 : 0 < risingFact ((r:ℝ)/2+1) k := risingFact_arg_pos hr k
  have hmono : risingFact (1/2+1) k ≤ risingFact ((r:ℝ)/2+1) k := risingFact_mono_arg hr k
  have h1 : (risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))
      ≤ (risingFact (1/2) k)^2 / (risingFact (1/2+1) k * (k.factorial:ℝ)) := by
    apply div_le_div_of_nonneg_left (le_of_lt hsq) (by positivity)
    exact mul_le_mul_of_nonneg_right hmono (le_of_lt hfk)
  calc Cr r * (risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))
      = Cr r * ((risingFact (1/2) k)^2 / (risingFact ((r:ℝ)/2+1) k * (k.factorial:ℝ))) := by
        field_simp
    _ ≤ Cr r * ((risingFact (1/2) k)^2 / (risingFact (1/2+1) k * (k.factorial:ℝ))) := by
        apply mul_le_mul_of_nonneg_left h1 (le_of_lt hC)
    _ = Cr r * (bc k / (2*(k:ℝ)+1)) := by
        rw [risingFact_three_half]
        unfold bc
        have h2k : (0:ℝ) < 2*(k:ℝ)+1 := by positivity
        have hrf : (0:ℝ) < risingFact (1/2) k := risingFact_half_pos k
        field_simp

lemma summable_ErCoeff {r : ℕ} (hr : 1 ≤ r) : Summable (fun k : ℕ => ErCoeff r k) := by
  have h := summable_bc_div.mul_left (Cr r)
  exact Summable.of_nonneg_of_le (fun k => ErCoeff_nonneg hr k) (fun k => ErCoeff_le hr k) h

/-- `Er r` is continuous on `[-1,1]` for every `r ≥ 1`. -/
lemma continuousOn_Er {r : ℕ} (hr : 1 ≤ r) : ContinuousOn (fun t => Er r t) (Set.Icc (-1:ℝ) 1) := by
  have hu := summable_ErCoeff hr
  have hb : ∀ (n : ℕ) (x : ℝ), x ∈ Set.Icc (-1:ℝ) 1 →
      ‖ErCoeff r n * x^(2*n+1)‖ ≤ ErCoeff r n := by
    intro n x hx
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hlt : |x|^(2*n+1) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_nonneg hr n)]
    calc ErCoeff r n * |x|^(2*n+1) ≤ ErCoeff r n * 1 :=
          mul_le_mul_of_nonneg_left hlt (ErCoeff_nonneg hr n)
      _ = ErCoeff r n := by ring
  have hunif := tendstoUniformlyOn_tsum hu hb
  have hcont : ∀ (s : Finset ℕ), ContinuousOn
      (fun t : ℝ => ∑ k ∈ s, ErCoeff r k * t^(2*k+1)) (Set.Icc (-1:ℝ) 1) := by
    intro s
    have hc : Continuous (fun t : ℝ => ∑ k ∈ s, ErCoeff r k * t^(2*k+1)) := by
      apply continuous_finset_sum
      intro k _
      fun_prop
    exact hc.continuousOn
  exact hunif.continuousOn (Eventually.of_forall hcont).frequently

/-- `Er r` is monotone on `[0,1]` for `r ≥ 1`. -/
lemma Er_mono {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hst : s ≤ t) : Er r s ≤ Er r t := by
  have hsum : Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
    · exact mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg ht.1 _)
    · calc ErCoeff r k * t^(2*k+1) ≤ ErCoeff r k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 (by linarith [ht.2]))
              (ErCoeff_nonneg hr k)
        _ = ErCoeff r k := by ring
  have hsum_s : Summable (fun k : ℕ => ErCoeff r k * s^(2*k+1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
    · exact mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg hs.1 _)
    · calc ErCoeff r k * s^(2*k+1) ≤ ErCoeff r k * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hs.1 (by linarith [hs.2]))
              (ErCoeff_nonneg hr k)
        _ = ErCoeff r k := by ring
  have hle : ∀ k, ErCoeff r k * s^(2*k+1) ≤ ErCoeff r k * t^(2*k+1) := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (ErCoeff_nonneg hr k)
    apply pow_le_pow_left₀ hs.1 hst
  rw [Er, Er]
  exact Summable.tsum_le_tsum hle hsum_s hsum

lemma Er_mono_summable {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (summable_ErCoeff hr)
  · exact mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg h0 _)
  · calc ErCoeff r k * t^(2*k+1) ≤ ErCoeff r k * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (ErCoeff_nonneg hr k)
      _ = ErCoeff r k := by ring

/-! ## 8b. Strict monotonicity of `Er r` on `[0,1]` -/

lemma pow_sub_pow_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (m : ℕ) :
    0 ≤ t^(2*m+1) - s^(2*m+1) :=
  sub_nonneg.mpr (pow_le_pow_left₀ hs hst _)

/-- `Er r` is strictly increasing on `[0,1]` for `r ≥ 1`. -/
theorem Er_strictMono {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (ht : t ≤ 1) : Er r s < Er r t := by
  have hstle : s ≤ t := le_of_lt hst
  have hs1 : s ≤ 1 := le_trans hstle ht
  -- summability of the difference series
  have ht0 : (0:ℝ) ≤ t := le_trans hs hstle
  have hdiff : Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) :=
    (Er_mono_summable hr ht0 ht).sub (Er_mono_summable hr hs hs1)
  have hnonneg : ∀ k, 0 ≤ (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) := by
    intro k
    have h := pow_sub_pow_nonneg hs hstle k
    have h2 : ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)
        = ErCoeff r k * (t^(2*k+1) - s^(2*k+1)) := by ring
    rw [h2]
    exact mul_nonneg (ErCoeff_nonneg hr k) h
  have hpos0 : 0 < ErCoeff r 0 * t^(2*0+1) - ErCoeff r 0 * s^(2*0+1) := by
    have hC : 0 < Cr r := Cr_pos hr
    have hE0 : ErCoeff r 0 = Cr r := by
      unfold ErCoeff
      norm_num [risingFact]
    have hE : 0 < ErCoeff r 0 := by rw [hE0]; exact hC
    have hpow : ∀ x : ℝ, x^(2*0+1) = x := by intro x; norm_num
    have : ErCoeff r 0 * t^(2*0+1) - ErCoeff r 0 * s^(2*0+1) = ErCoeff r 0 * (t - s) := by
      rw [hpow t, hpow s]; ring
    rw [this]
    exact mul_pos hE (sub_pos.mpr hst)
  have htsum : 0 < ∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)) :=
    hdiff.tsum_pos hnonneg 0 hpos0
  have hsplit : (∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)))
      = Er r t - Er r s := by
    show (∑' k : ℕ, (ErCoeff r k * t^(2*k+1) - ErCoeff r k * s^(2*k+1)))
        = (∑' k : ℕ, ErCoeff r k * t^(2*k+1)) - (∑' k : ℕ, ErCoeff r k * s^(2*k+1))
    rw [Summable.tsum_sub (Er_mono_summable hr ht0 ht) (Er_mono_summable hr hs hs1)]
  rw [hsplit] at htsum
  linarith

/-! ## 8c. Oddness and injectivity of `Er r` -/

lemma summable_Er_abs {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) :
    Summable (fun k : ℕ => ErCoeff r k * t^(2*k+1)) := by
  have hb : ∀ k : ℕ, ‖ErCoeff r k * t^(2*k+1)‖ ≤ ErCoeff r k := by
    intro k
    have h1 : |t|^(2*k+1) ≤ 1 := (pow_le_one₀ (abs_nonneg t) ht : |t|^(2*k+1) ≤ 1)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (ErCoeff_nonneg hr k)]
    calc ErCoeff r k * |t|^(2*k+1) ≤ ErCoeff r k * 1 :=
          mul_le_mul_of_nonneg_left h1 (ErCoeff_nonneg hr k)
      _ = ErCoeff r k := by ring
  exact Summable.of_norm_bounded (summable_ErCoeff hr) hb

lemma neg_pow_odd (t : ℝ) (k : ℕ) : (-t)^(2*k+1) = -(t^(2*k+1)) := by
  rw [neg_pow]
  have h1 : (-1:ℝ)^(2*k+1) = -1 := by
    rw [show 2*k+1 = 2*k + 1 by ring, pow_succ, Even.neg_one_pow ⟨k, by ring⟩]
    ring
  rw [h1]
  ring

/-- `Er r` is odd. -/
theorem Er_neg {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : |t| ≤ 1) : Er r (-t) = -Er r t := by
  have hcongr : (fun k : ℕ => ErCoeff r k * (-t)^(2*k+1))
      = fun k : ℕ => -(ErCoeff r k * t^(2*k+1)) := by
    funext k
    rw [neg_pow_odd t k]
    ring
  rw [Er, hcongr, tsum_neg]
  rfl

/-- `Er r` is injective on `[0,1]` for `r ≥ 1`. -/
theorem Er_injOn_Icc {r : ℕ} (hr : 1 ≤ r) : Set.InjOn (Er r) (Set.Icc (0:ℝ) 1) := by
  intro s hs t ht h
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact absurd h (ne_of_lt (Er_strictMono hr hs.1 hlt ht.2))
  · exact heq
  · exact absurd h.symm (ne_of_lt (Er_strictMono hr ht.1 hgt hs.2))

/-- The `r = 1` instance of Gauss's evaluation `E_r(1) = 1`. -/
theorem Er_one_one : Er 1 1 = 1 := by
  have h := Er_one_Icc (t := 1) (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have harc : Real.arcsin 1 = Real.pi / 2 := Real.arcsin_eq_pi_div_two.mpr le_rfl
  rw [harc] at h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  rw [h]
  field_simp

/-- `E_1` maps `[-1,1]` into `[-1,1]`. -/
theorem Er_one_maps (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Er 1 t ∈ Set.Icc (-1:ℝ) 1 :=
  Set.mem_Icc.mpr ⟨neg_le_of_abs_le (abs_Er_one_le_one ht), le_of_abs_le (abs_Er_one_le_one ht)⟩

end Grothendieck

/-! ## 9. Axiom check -/

namespace Grothendieck

/-! ## Strict monotonicity on the whole interval `[-1,1]` -/

/-- `Er r t > 0` for `0 < t ≤ 1`: every coefficient is nonnegative and the first term is `Cr r * t`. -/
theorem Er_pos {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) : 0 < Er r t := by
  have hsum := Er_mono_summable hr (le_of_lt h0) h1
  have hnn : ∀ k : ℕ, 0 ≤ ErCoeff r k * t ^ (2 * k + 1) := fun k =>
    mul_nonneg (ErCoeff_nonneg hr k) (pow_nonneg (le_of_lt h0) _)
  have hle : ErCoeff r 0 * t ^ (2 * 0 + 1) ≤ Er r t := by
    have := hsum.sum_le_tsum {0} (fun i hi => hnn i)
    simpa [Er] using this
  have hfirst : 0 < ErCoeff r 0 * t ^ (2 * 0 + 1) := by
    have hc : 0 < ErCoeff r 0 := by
      simpa [ErCoeff, risingFact] using Cr_pos hr
    simpa using mul_pos hc h0
  linarith

/-- **`Er r` is strictly increasing on `[-1,1]`**, hence injective there: this is what makes
`ErInv` (the paper's `E_r⁻¹`) the genuine inverse of `E_r` on its interval. -/
theorem Er_strictMono_Icc {r : ℕ} (hr : 1 ≤ r) {s t : ℝ}
    (hs : s ∈ Set.Icc (-1 : ℝ) 1) (hst : s < t) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Er r s < Er r t := by
  have hsa : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
  have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  by_cases h0 : 0 ≤ s
  · exact Er_strictMono hr h0 hst ht.2
  · have hneg : s < 0 := not_le.mp h0
    by_cases ht0 : t ≤ 0
    · have h1 : 0 ≤ -t := by linarith
      have h2 : -t < -s := by linarith
      have h3 : -s ≤ 1 := by linarith [hs.1]
      have h := Er_strictMono hr h1 h2 h3
      rw [Er_neg hr hta, Er_neg hr hsa] at h
      linarith
    · have htpos : 0 < t := not_le.mp ht0
      have hspos : Er r s < 0 := by
        have hp := Er_pos hr (t := -s) (by linarith) (by linarith [hs.1])
        rw [Er_neg hr hsa] at hp
        linarith
      have htpos' : 0 < Er r t := Er_pos hr htpos ht.2
      linarith

end Grothendieck

namespace Grothendieck

/-- `Cr 3 = 8/(3π)`, the rank-three constant of the paper. -/
theorem Cr_three : Cr 3 = 8 / (3 * Real.pi) := by
  have h3 : Real.Gamma (3/2) = Real.sqrt Real.pi / 2 := by
    have h := Real.Gamma_add_one (s := (1/2:ℝ)) (by norm_num)
    rw [show (1/2:ℝ) + 1 = 3/2 by norm_num] at h
    rw [h, Real.Gamma_one_half_eq]; ring
  have h2 : Real.Gamma (2:ℝ) = 1 := Real.Gamma_two
  unfold Cr
  simp only [Nat.cast_ofNat]
  have e1 : ((3:ℝ) + 1) / 2 = 2 := by norm_num
  have e2 : (3:ℝ) / 2 = 3/2 := by norm_num
  rw [e1, e2, h2, h3]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  rw [Real.sq_sqrt (le_of_lt Real.pi_pos)]
  ring

/-- **The rank-three coefficients.** All coefficients of `E_3` are nonnegative, the sequence is
summable, and its first two terms are `8/(3π)` and `4/(15π)`. -/
theorem Er_three_coeff_proof :
    (∀ k : ℕ, 0 ≤ ErCoeff 3 k) ∧ Summable (fun k : ℕ => ErCoeff 3 k) ∧
      ErCoeff 3 0 = 8 / (3 * Real.pi) ∧ ErCoeff 3 1 = 4 / (15 * Real.pi) := by
  have hr : (1:ℕ) ≤ 3 := by norm_num
  refine ⟨fun k => ErCoeff_nonneg hr k, summable_ErCoeff hr, ?_, ?_⟩
  · have h0 : ErCoeff 3 0 = Cr 3 := by simp [ErCoeff, risingFact]
    rw [h0, Cr_three]
  · have h : ErCoeff 3 1 = Cr 3 * (1/2)^2 / ((3/2 + 1) * 1) := by
      simp [ErCoeff, risingFact]
    rw [h, Cr_three]
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

end Grothendieck

open Grothendieck in
theorem solution :
    (∀ k : ℕ, 0 ≤ ErCoeff 3 k) ∧ Summable (fun k : ℕ => ErCoeff 3 k) ∧
      ErCoeff 3 0 = 8 / (3 * Real.pi) ∧ ErCoeff 3 1 = 4 / (15 * Real.pi) :=
  Er_three_coeff_proof
