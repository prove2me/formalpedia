-- Prove2me | solution 1 for MVSieve.large_sieve_weight_lower
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-06T04:39:34.385765+00:00
-- url     : https://prove2.me/submissions/b4b7c456-b381-4111-926d-a8b13c56bb8c

import Mathlib
import Theorems.Thm_TaoFivePrimes_log_le_sum_moebius_sq_div_totient

/-! Lower bound for the large-sieve weight (Montgomery–Vaughan Lemmas 3 and 8 analogue).
The coprime splitting is adapted from the accepted platform proof of `TaoFivePrimes.mertens_coprime_split`
(Apache-2.0), with the primes `≤ Q` replaced by the prime factors of `r`. -/

open Finset

namespace MVWeight

/-- The weight `mu^2(n)/phi(n)`. -/
noncomputable def wt (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℝ)) ^ 2 / (Nat.totient n : ℝ)

theorem wt_nonneg (n : ℕ) : 0 ≤ wt n := by
  unfold wt; positivity

theorem wt_of_squarefree {n : ℕ} (h : Squarefree n) : wt n = 1 / (Nat.totient n : ℝ) := by
  unfold wt
  have : ((ArithmeticFunction.moebius n : ℝ)) ^ 2 = 1 := by
    have h1 : (ArithmeticFunction.moebius n) ^ 2 = 1 :=
      ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
  rw [this]

theorem wt_of_not_squarefree {n : ℕ} (h : ¬ Squarefree n) : wt n = 0 := by
  unfold wt
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  simp

/-- The totient of a product of distinct primes. -/
theorem totient_prod_primes :
    ∀ (t : Finset ℕ), (∀ p ∈ t, p.Prime) → Nat.totient (∏ p ∈ t, p) = ∏ p ∈ t, (p - 1) := by
  intro t
  induction t using Finset.induction_on with
  | empty => intro _; simp
  | insert p t hp ih =>
      intro hpr
      have hpprime : p.Prime := hpr p (Finset.mem_insert_self p t)
      have htpr : ∀ r ∈ t, r.Prime := fun r hr => hpr r (Finset.mem_insert_of_mem hr)
      have hcop : Nat.Coprime p (∏ r ∈ t, r) :=
        Nat.Coprime.prod_right (fun r hr =>
          (Nat.coprime_primes hpprime (htpr r hr)).mpr (by rintro rfl; exact hp hr))
      rw [Finset.prod_insert hp, Nat.totient_mul hcop, Nat.totient_prime hpprime,
        Finset.prod_insert hp, ih htpr]

theorem squarefree_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (ht p hp).squarefree)
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (ht a ha) (ht b hb)).mpr hab

theorem wt_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    wt (∏ p ∈ t, p) = ∏ p ∈ t, (1 / ((p : ℝ) - 1)) := by
  have hsq : Squarefree (∏ p ∈ t, p) := squarefree_prod_primes t ht
  rw [wt_of_squarefree hsq, totient_prod_primes t ht, Nat.cast_prod, one_div,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have h1 : 1 ≤ p := (ht p hp).one_lt.le
  rw [one_div]
  congr 1
  push_cast [Nat.cast_sub h1]
  ring

/-- Multiplicativity of the weight on coprime squarefree arguments. -/
theorem wt_mul {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) (hab : Nat.Coprime a b) :
    wt (a * b) = wt a * wt b := by
  have hsq : Squarefree (a * b) := (Nat.squarefree_mul_iff.mpr ⟨hab, ha, hb⟩)
  rw [wt_of_squarefree hsq, wt_of_squarefree ha, wt_of_squarefree hb,
    Nat.totient_mul hab, Nat.cast_mul]
  field_simp

/-- The prime factors of the modulus `r`. -/
def PQ (Q : ℕ) : Finset ℕ := Q.primeFactors

theorem prime_of_mem_PQ {Q p : ℕ} (h : p ∈ PQ Q) : p.Prime := Nat.prime_of_mem_primeFactors h

/-- The set of small prime factors of `n`. -/
def tp (Q n : ℕ) : Finset ℕ := n.primeFactors ∩ PQ Q

/-- The set of large prime factors of `n`. -/
def sp (Q n : ℕ) : Finset ℕ := n.primeFactors \ PQ Q

/-- The `Q`-smooth part of a squarefree `n`. -/
def dpt (Q n : ℕ) : ℕ := ∏ p ∈ tp Q n, p

/-- The `Q`-rough part of a squarefree `n`. -/
def mpt (Q n : ℕ) : ℕ := ∏ p ∈ sp Q n, p

theorem tp_prime {Q n p : ℕ} (h : p ∈ tp Q n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp h).1

theorem sp_prime {Q n p : ℕ} (h : p ∈ sp Q n) : p.Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp h).1

theorem tp_subset (Q n : ℕ) : tp Q n ⊆ PQ Q := Finset.inter_subset_right

theorem dpt_mul_mpt {Q n : ℕ} (hn : Squarefree n) : dpt Q n * mpt Q n = n := by
  rw [dpt, mpt, tp, sp, Finset.prod_inter_mul_prod_sdiff]
  exact Nat.prod_primeFactors_of_squarefree hn

theorem mpt_squarefree (Q n : ℕ) : Squarefree (mpt Q n) :=
  squarefree_prod_primes _ (fun p hp => sp_prime hp)

theorem dpt_squarefree (Q n : ℕ) : Squarefree (dpt Q n) :=
  squarefree_prod_primes _ (fun p hp => tp_prime hp)

theorem coprime_dpt_mpt (Q n : ℕ) : Nat.Coprime (dpt Q n) (mpt Q n) := by
  rw [dpt, mpt]
  refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun r hr => ?_))
  refine (Nat.coprime_primes (tp_prime hp) (sp_prime hr)).mpr ?_
  rintro rfl
  exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_inter.mp hp).2

theorem wt_split {Q n : ℕ} (hn : Squarefree n) :
    wt n = (∏ p ∈ tp Q n, (1 / ((p : ℝ) - 1))) * wt (mpt Q n) := by
  conv_lhs => rw [← dpt_mul_mpt (Q := Q) hn]
  rw [wt_mul (dpt_squarefree Q n) (mpt_squarefree Q n) (coprime_dpt_mpt Q n),
    dpt, wt_prod_primes _ (fun p hp => tp_prime hp)]

/-- The `Q`-rough integers up to `R`. -/
def MR (Q R : ℕ) : Finset ℕ := (Finset.Icc 1 R).filter (fun m => ∀ p ∈ PQ Q, ¬ p ∣ m)

theorem mpt_mem_MR {Q R n : ℕ} (hn : Squarefree n) (hnR : n ∈ Finset.Icc 1 R) :
    mpt Q n ∈ MR Q R := by
  rw [Finset.mem_Icc] at hnR
  have hn0 : n ≠ 0 := by omega
  have hdvd : mpt Q n ∣ n :=
    ⟨dpt Q n, by rw [mul_comm]; exact (dpt_mul_mpt (Q := Q) hn).symm⟩
  have hpos : 0 < mpt Q n := Nat.pos_of_ne_zero (by
    intro h; rw [h] at hdvd; exact hn0 (Nat.eq_zero_of_zero_dvd hdvd))
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, ?_⟩, ?_⟩
  · exact le_trans (Nat.le_of_dvd (by omega) hdvd) hnR.2
  · intro p hp hpd
    have hpp : p.Prime := prime_of_mem_PQ hp
    obtain ⟨r, hr, hrd⟩ := (Nat.Prime.prime hpp).exists_mem_finset_dvd hpd
    have : p = r := (Nat.prime_dvd_prime_iff_eq hpp (sp_prime hr)).mp hrd
    exact (Finset.mem_sdiff.mp hr).2 (this ▸ hp)

/-- The Mertens-type splitting: removing the primes up to `Q` from the modulus costs at most
the Euler product `∏_{p ≤ Q} p/(p-1)`. -/
theorem mertens_split (Q R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R, wt n)
      ≤ (∑ m ∈ MR Q R, wt m) * ∏ p ∈ PQ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 R).filter Squarefree with hS
  set F : ℕ → Finset ℕ × ℕ := fun n => (tp Q n, mpt Q n) with hF
  set g : Finset ℕ × ℕ → ℝ := fun z => (∏ p ∈ z.1, (1 / ((p : ℝ) - 1))) * wt z.2 with hg
  have hgnn : ∀ z ∈ (PQ Q).powerset ×ˢ MR Q R, 0 ≤ g z := by
    intro z hz
    have hz1 : z.1 ⊆ PQ Q := Finset.mem_powerset.mp (Finset.mem_product.mp hz).1
    refine mul_nonneg (Finset.prod_nonneg (fun p hp => ?_)) (wt_nonneg _)
    have hp2 : 2 ≤ p := (prime_of_mem_PQ (hz1 hp)).two_le
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : (0:ℝ) < (p:ℝ) - 1 := by linarith
    positivity
  -- step 1: only squarefree numbers contribute
  have hstep1 : (∑ n ∈ Finset.Icc 1 R, wt n) = ∑ n ∈ S, wt n := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hns
    exact wt_of_not_squarefree (fun h => hns (Finset.mem_filter.mpr ⟨hn, h⟩))
  -- step 2: reindex by (small primes, rough part)
  have hinj : ∀ n ∈ S, ∀ n' ∈ S, F n = F n' → n = n' := by
    intro n hn n' hn' h
    have h1 : tp Q n = tp Q n' := congrArg Prod.fst h
    have h2 : mpt Q n = mpt Q n' := congrArg Prod.snd h
    have hsq : Squarefree n := (Finset.mem_filter.mp hn).2
    have hsq' : Squarefree n' := (Finset.mem_filter.mp hn').2
    have := dpt_mul_mpt (Q := Q) hsq
    have := dpt_mul_mpt (Q := Q) hsq'
    rw [← dpt_mul_mpt (Q := Q) hsq, ← dpt_mul_mpt (Q := Q) hsq', dpt, dpt, h1, h2]
  have hstep2 : (∑ n ∈ S, wt n) = ∑ z ∈ S.image F, g z := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    exact wt_split (Q := Q) (Finset.mem_filter.mp hn).2
  -- step 3: the image sits inside a product set
  have hsubset : S.image F ⊆ (PQ Q).powerset ×ˢ MR Q R := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (tp_subset Q n), ?_⟩
    exact mpt_mem_MR (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hn).1
  have hstep3 : (∑ z ∈ S.image F, g z) ≤ ∑ z ∈ (PQ Q).powerset ×ˢ MR Q R, g z :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun z hz _ => hgnn z hz)
  -- step 4: factor the product sum
  have hstep4 : (∑ z ∈ (PQ Q).powerset ×ˢ MR Q R, g z)
      = (∑ t ∈ (PQ Q).powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1))) * ∑ m ∈ MR Q R, wt m := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
  -- step 5: the Euler product
  have hstep5 : (∑ t ∈ (PQ Q).powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1)))
      = ∏ p ∈ PQ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
    have := Finset.prod_add (fun p : ℕ => (1 / ((p : ℝ) - 1))) (fun _ : ℕ => (1 : ℝ)) (PQ Q)
    simp only [Finset.prod_const_one, mul_one] at this
    rw [← this]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp2 : 2 ≤ p := (prime_of_mem_PQ hp).two_le
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hstep1, hstep2]
  calc (∑ z ∈ S.image F, g z)
      ≤ ∑ z ∈ (PQ Q).powerset ×ˢ MR Q R, g z := hstep3
    _ = (∑ t ∈ (PQ Q).powerset, ∏ p ∈ t, (1 / ((p : ℝ) - 1))) * ∑ m ∈ MR Q R, wt m := hstep4
    _ = (∑ m ∈ MR Q R, wt m) * ∏ p ∈ PQ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
        rw [hstep5]; ring

theorem MR_eq_coprime {r : ℕ} (hr : r ≠ 0) (R : ℕ) :
    MR r R = (Finset.Icc 1 R).filter (fun m => Nat.Coprime m r) := by
  unfold MR
  refine Finset.filter_congr (fun m _ => ?_)
  constructor
  · intro h
    exact Nat.coprime_of_dvd (fun p hp hpm hpr =>
      h p (Nat.mem_primeFactors.mpr ⟨hp, hpr, hr⟩) hpm)
  · intro h p hp hpm
    have hp' := Nat.mem_primeFactors.mp hp
    have hc : Nat.Coprime p r := Nat.Coprime.coprime_dvd_left hpm h
    exact (Nat.Prime.coprime_iff_not_dvd hp'.1).mp hc hp'.2.1

theorem euler_prod {r : ℕ} (hr : r ≠ 0) :
    ∏ p ∈ PQ r, ((p : ℝ) / ((p : ℝ) - 1)) = (r : ℝ) / (r.totient : ℝ) := by
  have h := Nat.totient_mul_prod_primeFactors r
  have hcast : ((r.totient : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ))
      = (r : ℝ) * ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun z : ℕ => (z : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    push_cast [this]; ring
  have hpos : ∀ p ∈ r.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  have htot : (0 : ℝ) < r.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr)
  have hprod : (0 : ℝ) < ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos hpos
  rw [PQ, Finset.prod_div_distrib, div_eq_div_iff hprod.ne' htot.ne', mul_comm, hcast]

/-- `Σ_{n ≤ R} μ²(n)/φ(n) ≤ (r/φ(r)) Σ_{m ≤ R, (m,r)=1} μ²(m)/φ(m)`. -/
theorem split_coprime {r : ℕ} (hr : r ≠ 0) (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R, wt n)
      ≤ (r : ℝ) / (r.totient : ℝ) * ∑ m ∈ (Finset.Icc 1 R).filter (fun m => Nat.Coprime m r), wt m := by
  have h := mertens_split r R
  rw [MR_eq_coprime hr, euler_prod hr] at h
  linarith

/-- Partial summation: nonnegative partial sums against a nonnegative antitone weight. -/
theorem abel_nonneg (d h : ℕ → ℝ) (n : ℕ) (hD : ∀ k ≤ n, 0 ≤ ∑ i ∈ Finset.range k, d i)
    (hh : ∀ k, h (k + 1) ≤ h k) (h0 : ∀ k, 0 ≤ h k) :
    0 ≤ ∑ i ∈ Finset.range n, d i * h i := by
  have key : ∀ n, ∑ i ∈ Finset.range n, d i * h i
      = ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range (j + 1), d i) * (h j - h (j + 1))
        + (∑ i ∈ Finset.range n, d i) * h n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ (fun i => d i)]
        ring
  rw [key]
  refine add_nonneg (Finset.sum_nonneg (fun j hj => mul_nonneg ?_ ?_)) (mul_nonneg ?_ (h0 n))
  · exact hD (j + 1) (Finset.mem_range.mp hj)
  · linarith [hh j]
  · exact hD n le_rfl

theorem step_bound (x : ℝ) (hx : 1 ≤ x) (i : ℕ) :
    (Real.log (i + 3) - Real.log (x + i + 2)) - (Real.log (i + 2) - Real.log (x + i + 1))
      ≤ (Real.log (i + 2) - Real.log (i + 1)) * (x / (x + (i + 2))) := by
  set m : ℝ := (i : ℝ) + 2 with hm
  have hm2 : 2 ≤ m := by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
  have hb : 1 / m ≤ Real.log (i + 2) - Real.log (i + 1) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < m / (m - 1) by
      apply div_pos <;> linarith)
    rw [Real.log_div (by linarith) (by linarith)] at h
    have e1 : (i : ℝ) + 2 = m := rfl
    have e2 : (i : ℝ) + 1 = m - 1 := by rw [hm]; ring
    rw [e1, e2]
    have : 1 - (m / (m - 1))⁻¹ = 1 / m := by field_simp; ring
    linarith
  have h1 : Real.log (i + 3) - Real.log (i + 2) ≤ 1 / m := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m + 1) / m by
      apply div_pos <;> linarith)
    rw [Real.log_div (by linarith) (by linarith)] at h
    have e1 : (i : ℝ) + 3 = m + 1 := by rw [hm]; ring
    rw [e1]
    have : (m + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have h2 : 1 / (x + m) ≤ Real.log (x + i + 2) - Real.log (x + i + 1) := by
    have hpos : 0 < x + m - 1 := by linarith
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (x + m) / (x + m - 1) by
      apply div_pos <;> linarith)
    rw [Real.log_div (by linarith) (by linarith)] at h
    have e1 : x + (i : ℝ) + 2 = x + m := by rw [hm]; ring
    have e2 : x + (i : ℝ) + 1 = x + m - 1 := by rw [hm]; ring
    rw [e1, e2]
    have : 1 - ((x + m) / (x + m - 1))⁻¹ = 1 / (x + m) := by field_simp; ring
    linarith
  have hH : 0 < x / (x + m) := div_pos (by linarith) (by linarith)
  have key : 1 / m - 1 / (x + m) = (1 / m) * (x / (x + m)) := by field_simp; ring
  have : (1 / m) * (x / (x + m)) ≤ (Real.log (i + 2) - Real.log (i + 1)) * (x / (x + m)) :=
    mul_le_mul_of_nonneg_right hb hH.le
  have e3 : x + ((i : ℝ) + 2) = x + m := rfl
  rw [e3]
  linarith

/-- `Σ_{i<K} (log(i+1) - log i)·x/(x+i+1) ≥ log((x+1)/4)` for `K = ⌊x⌋ ≥ 1`. -/
theorem telescoping_lower (x : ℝ) (hx : 1 ≤ x) :
    Real.log ((x + 1) / 4) ≤ ∑ i ∈ Finset.range ⌊x⌋₊,
      (Real.log ((i : ℝ) + 1) - Real.log i) * (x / (x + ((i : ℝ) + 1))) := by
  have hK : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  obtain ⟨k, hk⟩ : ∃ k, ⌊x⌋₊ = k + 1 := ⟨⌊x⌋₊ - 1, by omega⟩
  have hxk : x < (k : ℝ) + 2 := by
    have := Nat.lt_floor_add_one x
    rw [hk] at this; push_cast at this; linarith
  rw [hk, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add, Real.log_one, Real.log_zero, sub_zero, zero_mul, add_zero]
  set f : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 2) - Real.log (x + i + 1) with hf
  have hsum : f k - f 0 ≤ ∑ i ∈ Finset.range k,
      (Real.log (((i + 1 : ℕ) : ℝ) + 1) - Real.log ((i + 1 : ℕ) : ℝ)) *
        (x / (x + (((i + 1 : ℕ) : ℝ) + 1))) := by
    rw [← Finset.sum_range_sub f k]
    refine Finset.sum_le_sum (fun i _ => ?_)
    have := step_bound x hx i
    simp only [hf]
    push_cast
    rw [show (i : ℝ) + 1 + 2 = i + 3 by ring, show x + ((i : ℝ) + 1) + 1 = x + i + 2 by ring,
      show (i : ℝ) + 1 + 1 = i + 2 by ring]
    exact this
  have hend : Real.log ((x + 1) / 4) ≤ f k - f 0 := by
    simp only [hf, Nat.cast_zero, add_zero, zero_add]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [Real.log_div (by linarith) (by norm_num)]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    -- log(k+2) - log(x+k+1) ≥ -log 2  since 2(k+2) ≥ x+k+1
    have hlt : Real.log (x + k + 1) ≤ Real.log 2 + Real.log ((k : ℝ) + 2) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    linarith
  linarith

theorem weight_lower_x {r : ℕ} (hr : r ≠ 0) (x : ℝ) (hx : 1 ≤ x) :
    Real.log ((x + 1) / 4) ≤ (r : ℝ) / (r.totient : ℝ) *
      ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m r), wt m * (x / (x + m)) := by
  classical
  set c : ℝ := (r : ℝ) / (r.totient : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  set K := ⌊x⌋₊ with hK
  let a : ℕ → ℝ := fun i => c * (if Nat.Coprime (i + 1) r then wt (i + 1) else 0)
  let b : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 1) - Real.log i
  let H : ℕ → ℝ := fun i => x / (x + ((i : ℝ) + 1))
  -- rewrite the coprime sums over `range`
  have hre : ∀ k : ℕ, ∀ g : ℕ → ℝ,
      ∑ m ∈ (Finset.Icc 1 k).filter (fun m => Nat.Coprime m r), g m
        = ∑ i ∈ Finset.range k, (if Nat.Coprime (i + 1) r then g (i + 1) else 0) := by
    intro k g
    have hI : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by ext; simp [Nat.lt_succ_iff]
    rw [Finset.sum_filter, hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [add_comm 1 i]
  have hA : ∀ k : ℕ, Real.log k ≤ ∑ i ∈ Finset.range k, a i := by
    intro k
    have h1 := TaoFivePrimes.log_le_sum_moebius_sq_div_totient (k : ℝ) (Nat.cast_nonneg k)
    rw [Nat.floor_natCast] at h1
    have h2 := split_coprime hr k
    rw [hre k wt, Finset.mul_sum] at h2
    have : ∑ i ∈ Finset.range k, a i
        = ∑ i ∈ Finset.range k, c * (if Nat.Coprime (i + 1) r then wt (i + 1) else 0) := rfl
    rw [this]
    calc Real.log k ≤ ∑ q ∈ Finset.Icc 1 k, wt q := by simpa only [wt] using h1
      _ ≤ _ := h2
  have hB : ∀ k : ℕ, ∑ i ∈ Finset.range k, b i = Real.log k := by
    intro k
    have := Finset.sum_range_sub (fun i : ℕ => Real.log (i : ℝ)) k
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, Real.log_zero, sub_zero] at this
    exact this
  have hab := abel_nonneg (fun i => a i - b i) H K
    (fun k _ => by rw [Finset.sum_sub_distrib, hB k]; linarith [hA k])
    (fun k => by
      simp only [H]
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      push_cast; linarith)
    (fun k => by simp only [H]; positivity)
  have hmain : ∑ i ∈ Finset.range K, b i * H i ≤ ∑ i ∈ Finset.range K, a i * H i := by
    have : ∑ i ∈ Finset.range K, (a i - b i) * H i
        = ∑ i ∈ Finset.range K, a i * H i - ∑ i ∈ Finset.range K, b i * H i := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
    linarith
  have htel := telescoping_lower x hx
  have hR : c * ∑ m ∈ (Finset.Icc 1 K).filter (fun m => Nat.Coprime m r), wt m * (x / (x + m))
      = ∑ i ∈ Finset.range K, a i * H i := by
    rw [hre K, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [a, H]
    split_ifs <;> push_cast <;> ring
  rw [hR]
  calc Real.log ((x + 1) / 4) ≤ ∑ i ∈ Finset.range K, b i * H i := htel
    _ ≤ _ := hmain

end MVWeight

/-- **Lower bound for the large-sieve weight**: for `N ≥ 16 Q²` and `r ≤ Q`,
`N · Σ_{m ≤ Q/r, (m,r)=1, μ²(m)=1} r/(φ(r)φ(m)(N + 16 r m Q)) ≥ log(Q/r) - log 4`. -/
theorem MVSieve.large_sieve_weight_lower_aux (Q : ℕ+) (N : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N)
    (r : ℕ+) (hr : r ≤ Q) :
    Real.log (((Q : ℕ) : ℝ) / ((r : ℕ) : ℝ)) - Real.log 4 ≤
      (N : ℝ) * ∑ m ∈ (Finset.Icc 1 (Q : ℕ)).filter
          (fun m => (r : ℕ) * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m),
        ((r : ℕ) : ℝ) / (((r : ℕ).totient : ℝ) * (m.totient : ℝ) *
          ((N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) := by
  classical
  have hr0 : (r : ℕ) ≠ 0 := r.ne_zero
  have hrpos : (0 : ℝ) < ((r : ℕ) : ℝ) := by exact_mod_cast r.pos
  have hQpos : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast Q.pos
  have hrQ : ((r : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast (PNat.coe_le_coe _ _).mpr hr
  set x : ℝ := ((Q : ℕ) : ℝ) / ((r : ℕ) : ℝ) with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hrpos]; linarith
  have hxr : x * ((r : ℕ) : ℝ) = ((Q : ℕ) : ℝ) := by rw [hx]; field_simp
  have h := MVWeight.weight_lower_x hr0 x hx1
  -- left side
  have hL : Real.log x - Real.log 4 ≤ Real.log ((x + 1) / 4) := by
    rw [Real.log_div (x := x + 1) (y := 4) (by linarith) (by norm_num)]
    linarith [Real.log_le_log (by linarith) (show x ≤ x + 1 by linarith)]
  -- drop non-squarefree terms and identify the index set
  have hset : ((Finset.Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m r)).filter Squarefree
      = (Finset.Icc 1 (Q : ℕ)).filter
          (fun m => (r : ℕ) * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hfl : m ≤ ⌊x⌋₊ ↔ (r : ℕ) * m ≤ Q := by
      rw [Nat.le_floor_iff (by linarith), hx, le_div_iff₀ hrpos]
      constructor
      · intro h'; have : ((m * (r : ℕ) : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) := by push_cast; linarith
        have := Nat.cast_le.mp this; linarith [mul_comm m (r : ℕ)]
      · intro h'; have : (((r : ℕ) * m : ℕ) : ℝ) ≤ ((Q : ℕ) : ℝ) := by exact_mod_cast h'
        push_cast at this; linarith
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      have h5 := hfl.mp h2
      refine ⟨⟨h1, ?_⟩, h5, h3.symm, h4⟩
      calc m ≤ (r : ℕ) * m := Nat.le_mul_of_pos_left m r.pos
        _ ≤ Q := h5
    · rintro ⟨⟨h1, -⟩, h5, h3, h4⟩
      exact ⟨⟨⟨h1, hfl.mpr h5⟩, h3.symm⟩, h4⟩
  have hdrop : ∑ m ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m r),
        MVWeight.wt m * (x / (x + m))
      = ∑ m ∈ (Finset.Icc 1 (Q : ℕ)).filter
          (fun m => (r : ℕ) * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m),
          (1 / (m.totient : ℝ)) * (x / (x + m)) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ Squarefree, hset]
    have hz : ∑ m ∈ ((Finset.Icc 1 ⌊x⌋₊).filter (fun m => Nat.Coprime m r)).filter
        (fun m => ¬ Squarefree m), MVWeight.wt m * (x / (x + m)) = 0 :=
      Finset.sum_eq_zero (fun m hm => by
        rw [MVWeight.wt_of_not_squarefree (Finset.mem_filter.mp hm).2, zero_mul])
    rw [hz, add_zero]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [MVWeight.wt_of_squarefree (Finset.mem_filter.mp hm).2.2.2]
  rw [hdrop, Finset.mul_sum] at h
  rw [Finset.mul_sum]
  refine le_trans hL (le_trans h (Finset.sum_le_sum (fun m hm => ?_)))
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
  have hφr : (0 : ℝ) < ((r : ℕ)).totient := by exact_mod_cast Nat.totient_pos.mpr r.pos
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNQ : 16 * ((Q : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hD : 0 < (N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ) := by positivity
  -- x/(x+m) ≤ N/(N + 16 r m Q)
  have hkey : x / (x + m) ≤ (N : ℝ) / ((N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ (by linarith) hD]
    push_cast
    have : x * (16 * (((r : ℕ) : ℝ) * m) * ((Q : ℕ) : ℝ)) = 16 * m * ((Q : ℕ) : ℝ) ^ 2 := by
      rw [show x * (16 * (((r : ℕ) : ℝ) * m) * ((Q : ℕ) : ℝ))
          = 16 * m * (x * ((r : ℕ) : ℝ)) * ((Q : ℕ) : ℝ) by ring, hxr]; ring
    nlinarith
  calc ((r : ℕ) : ℝ) / (((r : ℕ)).totient : ℝ) * (1 / (m.totient : ℝ) * (x / (x + m)))
      = ((r : ℕ) : ℝ) / ((((r : ℕ)).totient : ℝ) * (m.totient : ℝ)) * (x / (x + m)) := by
        field_simp
    _ ≤ ((r : ℕ) : ℝ) / ((((r : ℕ)).totient : ℝ) * (m.totient : ℝ)) *
        ((N : ℝ) / ((N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by field_simp

theorem solution (Q : ℕ+) (N : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N)
    (r : ℕ+) (hr : r ≤ Q) :
    Real.log (((Q : ℕ) : ℝ) / ((r : ℕ) : ℝ)) - Real.log 4 ≤
      (N : ℝ) * ∑ m ∈ (Finset.Icc 1 (Q : ℕ)).filter
          (fun m => (r : ℕ) * m ≤ Q ∧ Nat.Coprime r m ∧ Squarefree m),
        ((r : ℕ) : ℝ) / (((r : ℕ).totient : ℝ) * (m.totient : ℝ) *
          ((N : ℝ) + 16 * (((r : ℕ) * m : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) :=
  MVSieve.large_sieve_weight_lower_aux Q N hN r hr
