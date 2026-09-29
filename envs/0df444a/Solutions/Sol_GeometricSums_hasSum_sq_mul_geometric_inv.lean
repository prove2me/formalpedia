-- Prove2me | solution 1 for GeometricSums.hasSum_sq_mul_geometric_inv
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:12:28.72698+00:00
-- url     : https://prove2.me/submissions/4647e3ff-d400-41d3-9f81-06f1eed83b6f

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.MR.ShiuMoment =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# ShiuMoment — the block-divisor second-moment bound (S8 / MR-CORE, node P2)

The Matomäki–Radziwiłł moment computation (MR §6, Lemma 13; source
`docs/sources/mr_extract.md` §2.5, eq (18)) needs Shiu's bound

  `Σ_{Y ≤ n ≤ 2Y} g(n)² ≪ Y`

for the **block-divisor** function `g`, the multiplicative function with
`g(p^k) = k+1` for primes `p` in the dyadic block `[Y₁, 2Y₁]` and `g(p^k) = 1`
off the block.  Concretely `g n = #{ d ∣ n : d is block-smooth }`, i.e. the
number of divisors of `n` whose prime factors all lie in `[Y₁, 2Y₁]`; this is
`τ` of the block-part of `n`.

**Route taken: Route 2 (the Rankin / Euler-product route, the freeze's preferred
fallback).**  We work at `σ = 1` (no real powers needed — block primes are `≥ 2`
so the local geometric series converge).  The proof:

* reduce `Σ_{n ≤ M} g(n)²` to `M · Σ_{d block-smooth} τ(d)²/d` by a fibre over the
  block-part (`shiu_moment_reduce`);
* bound the block-restricted Euler product `Σ_{d block-smooth} τ(d)²/d` by the
  **absolute** constant `exp 14`, via mathlib's `EulerProduct` engine applied to a
  piecewise-multiplicative weight, whose local factor is
  `Σ_k (k+1)² p^{-k} = (1 + p⁻¹)/(1 - p⁻¹)³ ≤ exp(7/p)` and whose block-prime tail
  `Σ_{Y₁ ≤ p ≤ 2Y₁} 1/p ≤ 2` trivially (at most `Y₁+1` terms, each `≤ 1/Y₁`).

The exit stone `shiu_moment_sq` states `Σ_{Y ≤ n ≤ 2Y} g(n)² ≤ C·Y` with an
absolute `C` (independent of the block scale `Y₁` and the length `Y`), which feeds
wave-3/4 A2's Lemma-13 moment with the admitted `C^ℓ` slop.

Source pins (D5): MR arXiv v4 (`1501.04585v4`), §6 / eq (18).
-/

namespace Salt.MR

open Finset

/-- **Block-smoothness.**  Every prime factor of `n` lies in the dyadic block
`[Y₁, 2Y₁]`. -/
def BlockSmooth (Y₁ n : ℕ) : Prop := ∀ p ∈ n.primeFactors, Y₁ ≤ p ∧ p ≤ 2 * Y₁

instance (Y₁ n : ℕ) : Decidable (BlockSmooth Y₁ n) := by
  unfold BlockSmooth; infer_instance

/-- **The block-divisor function** `g`.  `g Y₁ n` = number of divisors of `n`
whose prime factors all lie in `[Y₁, 2Y₁]`, i.e. `τ` of the block-part of `n`.
On a block prime `p` one has `g Y₁ (p^k) = k+1`, off the block `g Y₁ (p^k) = 1`. -/
def blockDiv (Y₁ n : ℕ) : ℕ := (n.divisors.filter (BlockSmooth Y₁)).card

/-- **The Euler weight.**  `wt Y₁ n = τ(n)²/n` on block-smooth `n`, else `0`.
This is the multiplicative function fed to mathlib's `EulerProduct` engine:
summing it over `(2Y₁+1)`-smooth numbers picks out exactly the block-smooth `d`
(all other terms vanish), and its local factor at an off-block prime is `1`. -/
noncomputable def wt (Y₁ n : ℕ) : ℝ :=
  if BlockSmooth Y₁ n then (n.divisors.card : ℝ) ^ 2 / (n : ℝ) else 0

lemma wt_nonneg (Y₁ n : ℕ) : 0 ≤ wt Y₁ n := by
  unfold wt; split
  · positivity
  · exact le_refl 0

lemma blockSmooth_one (Y₁ : ℕ) : BlockSmooth Y₁ 1 := by
  intro p hp; simp at hp

lemma wt_one (Y₁ : ℕ) : wt Y₁ 1 = 1 := by
  unfold wt; rw [if_pos (blockSmooth_one Y₁)]; simp

/-! ## §2  The local Euler factor at a single prime -/

/-- **The block local factor.**  `Σ_k (k+1)² r^k = (1+r)/(1-r)³` for `r = p⁻¹`,
`p ≥ 2`.  Built from `2·Σ C(k+2,2) r^k − Σ C(k+1,1) r^k` via the identity
`(k+1)² = 2·C(k+2,2) − C(k+1,1)`. -/
lemma hasSum_local_block {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k)
      ((1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3) := by
  have hp1R : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.trans_lt' (by norm_num)
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact inv_lt_one_of_one_lt₀ hp1R
  have hnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have hne : (1 : ℝ) - r ≠ 0 := by linarith
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hnorm
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm
  have hcomb := (h2.mul_left 2).sub h1
  have hfun : (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * r ^ k)
      = fun n => 2 * (((n + 2).choose 2 : ℝ) * r ^ n) - ((n + 1).choose 1 : ℝ) * r ^ n := by
    funext n
    rw [Nat.cast_choose_two, Nat.choose_one_right]
    push_cast
    ring
  have hval : (1 + r) / (1 - r) ^ 3
      = 2 * (1 / (1 - r) ^ (2 + 1)) - 1 / (1 - r) ^ (1 + 1) := by
    norm_num; field_simp; ring
  rw [hfun, hval]
  exact hcomb

/-- The explicit value of `wt` on a prime power. -/
lemma wt_prime_pow (Y₁ : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    wt Y₁ (p ^ k)
      = if Y₁ ≤ p ∧ p ≤ 2 * Y₁ then ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k
        else if k = 0 then 1 else 0 := by
  unfold wt
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, Nat.divisors_one, Finset.card_singleton, Nat.cast_one, one_pow,
      div_one, if_pos (blockSmooth_one Y₁)]
    split <;> simp
  · have hk0 : k ≠ 0 := by omega
    have hpf : (p ^ k).primeFactors = {p} := Nat.primeFactors_prime_pow hk0 hp
    have hbs : BlockSmooth Y₁ (p ^ k) ↔ (Y₁ ≤ p ∧ p ≤ 2 * Y₁) := by
      unfold BlockSmooth; rw [hpf]; simp
    by_cases hblk : Y₁ ≤ p ∧ p ≤ 2 * Y₁
    · rw [if_pos (hbs.mpr hblk), if_pos hblk]
      have hcard : ((p ^ k).divisors.card : ℝ) = (k : ℝ) + 1 := by
        rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]; push_cast; ring
      rw [hcard, Nat.cast_pow, inv_pow, div_eq_mul_inv]
    · rw [if_neg (fun h => hblk (hbs.mp h)), if_neg hblk, if_neg hk0]

/-- The per-prime `tsum` of `wt`: the block local factor at a block prime, else `1`. -/
lemma wt_local_tsum (Y₁ : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, wt Y₁ (p ^ k)
      = if Y₁ ≤ p ∧ p ≤ 2 * Y₁ then (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3
        else 1 := by
  by_cases hblk : Y₁ ≤ p ∧ p ≤ 2 * Y₁
  · rw [if_pos hblk]
    have hfe : (fun k : ℕ => wt Y₁ (p ^ k))
        = fun k : ℕ => ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k := by
      funext k; rw [wt_prime_pow Y₁ hp k, if_pos hblk]
    rw [hfe]; exact (hasSum_local_block hp.two_le).tsum_eq
  · rw [if_neg hblk]
    have hfe : (fun k : ℕ => wt Y₁ (p ^ k))
        = fun k : ℕ => if k = 0 then (1 : ℝ) else 0 := by
      funext k; rw [wt_prime_pow Y₁ hp k, if_neg hblk]
    rw [hfe]; exact (hasSum_ite_eq 0 (1 : ℝ)).tsum_eq

/-- Per-prime norm-summability of `wt` (the sole `EulerProduct` hypothesis). -/
lemma wt_summable_prime (Y₁ : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => ‖wt Y₁ (p ^ k)‖) := by
  have hnn : (fun k : ℕ => ‖wt Y₁ (p ^ k)‖) = fun k => wt Y₁ (p ^ k) := by
    funext k; rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg _ _)]
  rw [hnn]
  by_cases hblk : Y₁ ≤ p ∧ p ≤ 2 * Y₁
  · have hfe : (fun k : ℕ => wt Y₁ (p ^ k))
        = fun k : ℕ => ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k := by
      funext k; rw [wt_prime_pow Y₁ hp k, if_pos hblk]
    rw [hfe]; exact (hasSum_local_block hp.two_le).summable
  · have hfe : (fun k : ℕ => wt Y₁ (p ^ k)) = fun k => if k = 0 then (1 : ℝ) else 0 := by
      funext k; rw [wt_prime_pow Y₁ hp k, if_neg hblk]
    rw [hfe]; exact (hasSum_ite_eq 0 (1 : ℝ)).summable

/-- `wt` is multiplicative on coprime arguments. -/
lemma wt_mul (Y₁ : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    wt Y₁ (m * n) = wt Y₁ m * wt Y₁ n := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; rw [mul_one, wt_one, mul_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; rw [one_mul, wt_one, one_mul]
  have hbs : BlockSmooth Y₁ (m * n) ↔ BlockSmooth Y₁ m ∧ BlockSmooth Y₁ n := by
    unfold BlockSmooth
    rw [Nat.primeFactors_mul hm hn]
    constructor
    · intro H
      exact ⟨fun p hp => H p (Finset.mem_union_left _ hp),
        fun p hp => H p (Finset.mem_union_right _ hp)⟩
    · rintro ⟨H1, H2⟩ p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact H1 p hp
      · exact H2 p hp
  unfold wt
  by_cases hM : BlockSmooth Y₁ m ∧ BlockSmooth Y₁ n
  · rw [if_pos (hbs.mpr hM), if_pos hM.1, if_pos hM.2, Nat.Coprime.card_divisors_mul h]
    have hmn : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hnn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    push_cast
    field_simp
  · rw [if_neg (fun hc => hM (hbs.mp hc))]
    rcases not_and_or.mp hM with h1 | h1
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h1, mul_zero]

/-- The block local factor is `≤ exp(7/p)` at block primes, `≤ exp 0 = 1` off block. -/
lemma wt_local_tsum_le_exp (Y₁ : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑' k : ℕ, wt Y₁ (p ^ k) ≤ Real.exp (if Y₁ ≤ p then 7 / (p : ℝ) else 0) := by
  rw [wt_local_tsum Y₁ hp]
  by_cases hblk : Y₁ ≤ p ∧ p ≤ 2 * Y₁
  · rw [if_pos hblk, if_pos hblk.1]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    set r : ℝ := (p : ℝ)⁻¹ with hr
    have hr0 : 0 < r := by rw [hr]; positivity
    have hr12 : r ≤ 1 / 2 := by
      rw [hr]; have h := inv_anti₀ (show (0 : ℝ) < 2 by norm_num) hp2
      rwa [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at h
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have hval_pos : (0 : ℝ) < (1 + r) / (1 - r) ^ 3 := by positivity
    have h7 : (7 : ℝ) / (p : ℝ) = 7 * r := by rw [hr]; ring
    rw [h7, ← Real.exp_log hval_pos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div (by positivity : (1 + r) ≠ 0) (by positivity : (1 - r) ^ 3 ≠ 0),
      Real.log_pow]
    have hA : Real.log (1 + r) ≤ r := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + r by linarith); linarith
    have hinv2 : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ h1r]; linarith
    have hB : -(2 * r) ≤ Real.log (1 - r) := by
      have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 - r)⁻¹ by positivity)
      rw [Real.log_inv] at hinv
      have heq : (1 - r)⁻¹ - 1 = r * (1 - r)⁻¹ := by
        field_simp; ring
      rw [heq] at hinv
      have hle2 : r * (1 - r)⁻¹ ≤ 2 * r := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hinv2 hr0.le
      linarith
    push_cast
    linarith [hA, hB]
  · rw [if_neg hblk]
    by_cases hle : Y₁ ≤ p
    · rw [if_pos hle]; exact Real.one_le_exp (by positivity)
    · rw [if_neg hle, Real.exp_zero]

/-! ## §3  The block-restricted Euler product is bounded by an absolute constant -/

/-- **The block-restricted Euler product bound.**  For any length `M` and block
scale `Y₁ ≥ 1`,
`Σ_{d ≤ M, d block-smooth} τ(d)²/d ≤ exp 14`.
The `EulerProduct` engine turns the sum over block-smooth `d` (all other `wt`
terms vanish) into `∏_{p ≤ 2Y₁} (local factor)`; off-block factors are `1`, block
factors are `≤ exp(7/p)`, and the block-prime tail `Σ_{Y₁ ≤ p ≤ 2Y₁} 7/p ≤ 14`
because there are at most `Y₁+1` such primes, each `≤ 1/Y₁`. -/
lemma block_tauSq_div_sum_le (Y₁ M : ℕ) (hY₁ : 1 ≤ Y₁) :
    ∑ d ∈ (Finset.Icc 1 M).filter (BlockSmooth Y₁), (d.divisors.card : ℝ) ^ 2 / (d : ℝ)
      ≤ Real.exp 14 := by
  classical
  set N : ℕ := 2 * Y₁ + 1 with hN
  set S := (Finset.Icc 1 M).filter (BlockSmooth Y₁) with hSdef
  have hconv : ∑ d ∈ S, (d.divisors.card : ℝ) ^ 2 / (d : ℝ) = ∑ d ∈ S, wt Y₁ d := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [hSdef, Finset.mem_filter] at hd
    rw [wt, if_pos hd.2]
  rw [hconv]
  have hmem : ∀ d ∈ S, d ∈ N.smoothNumbers := by
    intro d hd
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, hdb⟩ := hd
    rw [Nat.mem_smoothNumbers']
    intro p hpp hpd
    have hpf : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpd, by omega⟩
    have := hdb p hpf
    omega
  have hSum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := wt Y₁) (wt_one Y₁) (fun {m n} h => wt_mul Y₁ h)
      (fun {q} hq => wt_summable_prime Y₁ hq) N).2
  have hY₁R : (0 : ℝ) < (Y₁ : ℝ) := by exact_mod_cast hY₁
  have hSbound : ∑ p ∈ N.primesBelow, (if Y₁ ≤ p then 7 / (p : ℝ) else 0) ≤ 14 := by
    have hterm : ∀ p ∈ N.primesBelow, (if Y₁ ≤ p then 7 / (p : ℝ) else 0)
        ≤ (if Y₁ ≤ p then 7 / (Y₁ : ℝ) else 0) := by
      intro p _
      split
      · rename_i hle
        have hpR : (Y₁ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hle
        gcongr
      · exact le_refl 0
    calc ∑ p ∈ N.primesBelow, (if Y₁ ≤ p then 7 / (p : ℝ) else 0)
        ≤ ∑ p ∈ N.primesBelow, (if Y₁ ≤ p then 7 / (Y₁ : ℝ) else 0) :=
          Finset.sum_le_sum hterm
      _ = ∑ _p ∈ N.primesBelow.filter (Y₁ ≤ ·), (7 / (Y₁ : ℝ)) :=
          (Finset.sum_filter _ _).symm
      _ = ((N.primesBelow.filter (Y₁ ≤ ·)).card : ℝ) * (7 / (Y₁ : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Y₁ : ℝ) + 1) * (7 / (Y₁ : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hsub : N.primesBelow.filter (Y₁ ≤ ·) ⊆ Finset.Icc Y₁ (2 * Y₁) := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hp1, hp2⟩ := hp
            rw [Nat.mem_primesBelow] at hp1
            rw [Finset.mem_Icc]
            exact ⟨hp2, by omega⟩
          have hcard := Finset.card_le_card hsub
          rw [Nat.card_Icc] at hcard
          have hle : (N.primesBelow.filter (Y₁ ≤ ·)).card ≤ Y₁ + 1 := by omega
          exact_mod_cast hle
      _ ≤ 14 := by
          have h1Y : (1 : ℝ) ≤ (Y₁ : ℝ) := by exact_mod_cast hY₁
          have heq : ((Y₁ : ℝ) + 1) * (7 / (Y₁ : ℝ))
              = 7 * ((Y₁ : ℝ) + 1) / (Y₁ : ℝ) := by ring
          rw [heq, div_le_iff₀ hY₁R]
          linarith
  calc ∑ d ∈ S, wt Y₁ d
      = ∑ d ∈ S.subtype (· ∈ N.smoothNumbers), wt Y₁ ↑d :=
        (Finset.sum_subtype_of_mem (wt Y₁) hmem).symm
    _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, wt Y₁ (p ^ k) :=
        sum_le_hasSum _ (fun i _ => wt_nonneg _ _) hSum
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (if Y₁ ≤ p then 7 / (p : ℝ) else 0) := by
        refine Finset.prod_le_prod (fun p _ => tsum_nonneg (fun k => wt_nonneg _ _)) ?_
        intro p hp
        exact wt_local_tsum_le_exp Y₁ (Nat.mem_primesBelow.mp hp).2
    _ = Real.exp (∑ p ∈ N.primesBelow, (if Y₁ ≤ p then 7 / (p : ℝ) else 0)) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp 14 := Real.exp_le_exp.mpr hSbound

/-! ## §4  The block-part of `n` and `g n = τ(block-part n)` -/

/-- **The block-part of `n`.**  The largest block-smooth divisor of `n`:
`∏_{p ∈ [Y₁,2Y₁], p ∣ n} p^{v_p(n)}`, built as the `Finsupp.prod` of the
factorization filtered to block primes. -/
noncomputable def blockPart (Y₁ n : ℕ) : ℕ :=
  (n.factorization.filter (fun p => Y₁ ≤ p ∧ p ≤ 2 * Y₁)).prod (· ^ ·)

private lemma blockFactor_le (Y₁ n : ℕ) :
    n.factorization.filter (fun p => Y₁ ≤ p ∧ p ≤ 2 * Y₁) ≤ n.factorization := by
  rw [Finsupp.le_def]
  intro p
  rw [Finsupp.filter_apply]
  split
  · exact le_refl _
  · exact Nat.zero_le _

lemma blockPart_factorization (Y₁ n : ℕ) :
    (blockPart Y₁ n).factorization
      = n.factorization.filter (fun p => Y₁ ≤ p ∧ p ≤ 2 * Y₁) :=
  Nat.factorization_prod_pow_eq_self_of_le_factorization (blockFactor_le Y₁ n)

lemma blockPart_dvd (Y₁ n : ℕ) : blockPart Y₁ n ∣ n :=
  Nat.prod_pow_dvd_of_le_factorization (blockFactor_le Y₁ n)

lemma blockPart_pos (Y₁ n : ℕ) : 0 < blockPart Y₁ n := by
  rw [blockPart, Finsupp.prod]
  apply Finset.prod_pos
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter, Nat.support_factorization] at hp
  exact pow_pos (Nat.prime_of_mem_primeFactors hp.1).pos _

lemma blockSmooth_blockPart (Y₁ n : ℕ) : BlockSmooth Y₁ (blockPart Y₁ n) := by
  intro q hq
  rw [← Nat.support_factorization, blockPart_factorization, Finsupp.support_filter,
    Finset.mem_filter] at hq
  exact hq.2

/-- **`g n = τ(block-part n)`.**  The number of block-smooth divisors of `n` equals
`τ` of its block-part. -/
lemma blockDiv_eq_card_blockPart (Y₁ n : ℕ) (hn : n ≠ 0) :
    blockDiv Y₁ n = (blockPart Y₁ n).divisors.card := by
  unfold blockDiv
  congr 1
  ext e
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hedvd, _⟩, hbse⟩
    have he : e ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hedvd)
    refine ⟨?_, (blockPart_pos Y₁ n).ne'⟩
    rw [← Nat.factorization_le_iff_dvd he (blockPart_pos Y₁ n).ne', blockPart_factorization,
      Finsupp.le_def]
    intro p
    rw [Finsupp.filter_apply]
    by_cases hP : Y₁ ≤ p ∧ p ≤ 2 * Y₁
    · rw [if_pos hP]
      exact Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd he hn).mpr hedvd) p
    · rw [if_neg hP, Nat.le_zero]
      by_contra hne
      have hpp : p ∈ e.primeFactors := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]; exact hne
      exact hP (hbse p hpp)
  · rintro ⟨hedvd, _⟩
    refine ⟨⟨hedvd.trans (blockPart_dvd Y₁ n), hn⟩, fun p hp => ?_⟩
    exact blockSmooth_blockPart Y₁ n p
      (Nat.primeFactors_mono hedvd (blockPart_pos Y₁ n).ne' hp)

/-! ## §5  The fibre reduction and the exit stone -/

/-- **The fibre reduction.**  `Σ_{n ≤ M} g(n)² ≤ M · Σ_{d block-smooth} τ(d)²/d`.
Fibre `n` over its block-part `d = blockPart n`: on the fibre `g(n)² = τ(d)²` is
constant, and the fibre has `≤ ⌊M/d⌋ ≤ M/d` elements (all multiples of `d ∣ n`). -/
lemma shiu_moment_reduce (Y₁ M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (blockDiv Y₁ n : ℝ) ^ 2
      ≤ (M : ℝ) * ∑ d ∈ (Finset.Icc 1 M).filter (BlockSmooth Y₁),
          (d.divisors.card : ℝ) ^ 2 / (d : ℝ) := by
  classical
  have hmaps : ∀ n ∈ Finset.Icc 1 M,
      blockPart Y₁ n ∈ (Finset.Icc 1 M).filter (BlockSmooth Y₁) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨blockPart_pos Y₁ n, ?_⟩, blockSmooth_blockPart Y₁ n⟩
    exact le_trans (Nat.le_of_dvd (by omega) (blockPart_dvd Y₁ n)) hn.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, _⟩, _⟩ := hd
  have hconst : ∀ n ∈ (Finset.Icc 1 M).filter (fun n => blockPart Y₁ n = d),
      (blockDiv Y₁ n : ℝ) ^ 2 = (d.divisors.card : ℝ) ^ 2 := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, hbn⟩ := hn
    rw [blockDiv_eq_card_blockPart Y₁ n (by omega), hbn]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hsub : (Finset.Icc 1 M).filter (fun n => blockPart Y₁ n = d)
      ⊆ (Finset.Icc 1 M).filter (fun n => d ∣ n) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2 ▸ blockPart_dvd Y₁ n⟩
  have hcard2 : ((Finset.Icc 1 M).filter (fun n => d ∣ n)).card = M / d := by
    rw [← Nat.card_multiples' M d]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hkd⟩; exact ⟨by omega, by omega, hkd⟩
    · rintro ⟨hk1, hk2, hkd⟩; exact ⟨⟨by omega, by omega⟩, hkd⟩
  have hfcle : (((Finset.Icc 1 M).filter (fun n => blockPart Y₁ n = d)).card : ℝ)
      ≤ (M : ℝ) / (d : ℝ) := by
    have h1 := Finset.card_le_card hsub
    rw [hcard2] at h1
    calc (((Finset.Icc 1 M).filter (fun n => blockPart Y₁ n = d)).card : ℝ)
        ≤ ((M / d : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ (M : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hτ2 : (0 : ℝ) ≤ (d.divisors.card : ℝ) ^ 2 := by positivity
  calc (((Finset.Icc 1 M).filter (fun n => blockPart Y₁ n = d)).card : ℝ)
        * (d.divisors.card : ℝ) ^ 2
      ≤ ((M : ℝ) / (d : ℝ)) * (d.divisors.card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hfcle hτ2
    _ = (M : ℝ) * ((d.divisors.card : ℝ) ^ 2 / (d : ℝ)) := by ring

/-- **`shiu_moment_sq` — the exit stone (S8/MR-CORE node P2).**
`Σ_{Y ≤ n ≤ 2Y} g(n)² ≤ C · Y` for the block-divisor `g = blockDiv Y₁`, with an
**absolute** constant `C = 2·exp 14` (independent of the block scale `Y₁` and the
length `Y`).  This is MR eq (18) / Shiu's bound for the block-divisor function.
Feeds wave-3/4 A2's Lemma-13 moment (with the admitted `C^ℓ` slop). -/
theorem shiu_moment_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ Y : ℕ), 1 ≤ Y₁ →
      ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 ≤ C * (Y : ℝ) := by
  refine ⟨2 * Real.exp 14, by positivity, ?_⟩
  intro Y₁ Y hY₁
  have hg0 : (blockDiv Y₁ 0 : ℝ) ^ 2 = 0 := by simp [blockDiv]
  have hstep1 : ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := by
    have hsub : Finset.Icc Y (2 * Y) ⊆ insert 0 (Finset.Icc 1 (2 * Y)) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨hpos, hn.2⟩)
    calc ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2
        ≤ ∑ n ∈ insert 0 (Finset.Icc 1 (2 * Y)), (blockDiv Y₁ n : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = ∑ n ∈ Finset.Icc 1 (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := by
          rw [Finset.sum_insert (by simp), hg0, zero_add]
  calc ∑ n ∈ Finset.Icc Y (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 (2 * Y), (blockDiv Y₁ n : ℝ) ^ 2 := hstep1
    _ ≤ ((2 * Y : ℕ) : ℝ) * ∑ d ∈ (Finset.Icc 1 (2 * Y)).filter (BlockSmooth Y₁),
          (d.divisors.card : ℝ) ^ 2 / (d : ℝ) := shiu_moment_reduce Y₁ (2 * Y)
    _ ≤ ((2 * Y : ℕ) : ℝ) * Real.exp 14 :=
        mul_le_mul_of_nonneg_left (block_tauSq_div_sum_le Y₁ (2 * Y) hY₁) (by positivity)
    _ = 2 * Real.exp 14 * (Y : ℝ) := by push_cast; ring

end Salt.MR

end




theorem solution {p : ℕ} (hp : 2 ≤ p) :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * ((p : ℝ)⁻¹) ^ k)
      ((1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 3) := by
  apply Salt.MR.hasSum_local_block <;> assumption

