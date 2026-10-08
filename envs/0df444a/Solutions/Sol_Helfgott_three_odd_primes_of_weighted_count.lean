-- Prove2me | solution 1 for Helfgott.three_odd_primes_of_weighted_count
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T21:30:12.110975+00:00
-- url     : https://prove2.me/submissions/adeaf6e6-fbf9-4d17-9d31-538a88be9ee6

import Definitions.Def_Helfgott_PrimePowerRemoval
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
Elementary prime-power removal for Helfgott's ternary Goldbach argument,
arXiv:1312.7748v2, §7.4, (7.50). The proper-prime-power injection is adapted
from jjosh's ACCEPTED proof 0afb155e-9279-4986-8c71-52a437e3c0e2 on
Prove2Me (WeakGoldbach.prime_power_part_le_above_2e18). The ternary estimate
and the uniform numerical bound below are derived here. They replace the
quoted Rosser–Schoenfeld estimates by a weaker elementary bound that is
still sufficient at N ≥ 10^27.

Written by Codex.
-/

open Finset ArithmeticFunction
open scoped BigOperators

namespace Helfgott

theorem proper_prime_power_card (N : ℕ) :
    ((Finset.range (N + 1)).filter (fun x => IsPrimePow x ∧ ¬ x.Prime)).card
      ≤ (Nat.sqrt N + 1) * (Nat.log 2 N + 1) := by
  classical
  rw [← Finset.card_range (Nat.sqrt N + 1),
    ← Finset.card_range (Nat.log 2 N + 1), ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun x => (x.minFac, x.factorization x.minFac))
  · intro x hx
    obtain ⟨hxr, hpp, hnp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hxm : x ≤ N := by
      have := Finset.mem_range.mp hxr
      omega
    have hxpos : 0 < x := hpp.pos
    have hxne1 : x ≠ 1 := fun h1 => not_isPrimePow_one (h1 ▸ hpp)
    have hminp : x.minFac.Prime := Nat.minFac_prime hxne1
    have hmin2 : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self hxpos hnp
    have hfact_eq : x.minFac ^ x.factorization x.minFac = x :=
      hpp.minFac_pow_factorization_eq
    have hminfac_le : x.minFac ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      calc x.minFac * x.minFac = x.minFac ^ 2 := by ring
        _ ≤ x := hmin2
        _ ≤ N := hxm
    have h2e : 2 ^ x.factorization x.minFac ≤ N := by
      calc 2 ^ x.factorization x.minFac
          ≤ x.minFac ^ x.factorization x.minFac :=
            Nat.pow_le_pow_left (Nat.Prime.two_le hminp) _
        _ = x := hfact_eq
        _ ≤ N := hxm
    have hele : x.factorization x.minFac ≤ Nat.log 2 N :=
      Nat.le_log_of_pow_le (by norm_num) h2e
    apply Finset.mem_coe.mpr
    rw [Finset.mem_product]
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hminfac_le),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hele)⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    have hx₁' := Finset.mem_filter.mp (Finset.mem_coe.mp hx₁)
    have hx₂' := Finset.mem_filter.mp (Finset.mem_coe.mp hx₂)
    have e1 : x₁.minFac ^ x₁.factorization x₁.minFac = x₁ :=
      hx₁'.2.1.minFac_pow_factorization_eq
    have e2 : x₂.minFac ^ x₂.factorization x₂.minFac = x₂ :=
      hx₂'.2.1.minFac_pow_factorization_eq
    have hmf : x₁.minFac = x₂.minFac := congrArg Prod.fst heq
    have hexp : x₁.factorization x₁.minFac = x₂.factorization x₂.minFac :=
      congrArg Prod.snd heq
    rw [hmf] at hexp
    calc x₁ = x₁.minFac ^ x₁.factorization x₁.minFac := e1.symm
      _ = x₂.minFac ^ x₂.factorization x₂.minFac := by rw [hmf, hexp]
      _ = x₂ := e2

/-- The deliberately crude elementary bound leaves ample room below the
paper's positive weighted main term, 0.000422 N². -/
theorem prime_power_error_small (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    2 * 3 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ) *
        ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) ^ 3
      ≤ (1 / 5000 : ℝ) * (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNreal : (10 : ℝ) ^ 27 ≤ N := by exact_mod_cast hN
  set y : ℝ := (N : ℝ) ^ (1 / 16 : ℝ) with hydef
  have hypos : 0 < y := Real.rpow_pos_of_pos hNpos _
  have hy16 : y ^ (16 : ℕ) = N := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hy40 : (40 : ℝ) ≤ y := by
    have hbase : (40 : ℝ) ^ (16 : ℕ) ≤ N := by
      calc _ ≤ (10 : ℝ) ^ 27 := by norm_num
        _ ≤ N := hNreal
    calc (40 : ℝ) = ((40 : ℝ) ^ (16 : ℕ)) ^ (1 / 16 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 40)]
          norm_num
      _ ≤ y := Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hlogy : Real.log y ≤ y / 8 := by
    have ht := Real.log_le_sub_one_of_pos (div_pos hypos (by norm_num : (0 : ℝ) < 64))
    rw [Real.log_div hypos.ne' (by norm_num : (64 : ℝ) ≠ 0)] at ht
    have hlog64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [hlog64] at ht
    have hlog2 : Real.log 2 < (7 / 10 : ℝ) :=
      lt_trans Real.log_two_lt_d9 (by norm_num)
    linarith
  have hlogN : Real.log (N : ℝ) = 16 * Real.log y := by
    rw [← hy16, Real.log_pow]
    norm_num
  have hL : Real.log (N : ℝ) ≤ 2 * y := by rw [hlogN]; linarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hnatlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have hp : (2 : ℝ) ^ Nat.log 2 N ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 N) hp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hl
  have hlog2low : (2 / 3 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hnatlog' : (Nat.log 2 N : ℝ) + 1 ≤ 4 * y := by
    have hnn : (0 : ℝ) ≤ Nat.log 2 N := by positivity
    nlinarith
  have hsqrt : (Nat.sqrt N : ℝ) ≤ y ^ 8 := by
    have hsq : (Nat.sqrt N : ℝ) ^ 2 ≤ N := by
      have hsq' : Nat.sqrt N ^ 2 ≤ N := by simpa only [pow_two] using Nat.sqrt_le N
      exact_mod_cast hsq'
    have heq : (y ^ (8 : ℕ)) ^ 2 = N := by rw [← pow_mul]; norm_num; exact hy16
    nlinarith [sq_nonneg (Nat.sqrt N : ℝ), pow_nonneg hypos.le 8]
  have hy8one : (1 : ℝ) ≤ y ^ (8 : ℕ) := one_le_pow₀ hy1
  have hy9one : (1 : ℝ) ≤ y ^ (9 : ℕ) := one_le_pow₀ hy1
  have hsqrt' : (Nat.sqrt N : ℝ) + 1 ≤ 2 * y ^ 8 := by linarith
  have hcount : (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ)
      ≤ 10 * y ^ 9 := by
    push_cast
    have hmul := mul_le_mul hsqrt' hnatlog' (by positivity) (by positivity)
    have heq : (2 * y ^ 8) * (4 * y) = 8 * y ^ 9 := by ring
    rw [heq] at hmul
    linarith
  have hNsucc : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  have hLcube : Real.log (N : ℝ) ^ 3 ≤ (2 * y) ^ 3 :=
    pow_le_pow_left₀ hL0 hL 3
  have hprod : 2 * 3 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ) *
        ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) ^ 3
      ≤ 960 * (N : ℝ) * y ^ 12 := by
    calc _ ≤ 2 * 3 * (10 * y ^ 9) * (2 * (N : ℝ)) * (2 * y) ^ 3 := by
          apply mul_le_mul
          · apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hcount (by norm_num)
            · exact hNsucc
            · positivity
            · positivity
          · exact hLcube
          · positivity
          · positivity
      _ = _ := by ring
  have hy4 : (5000000 : ℝ) ≤ y ^ (4 : ℕ) := by
    by_contra h
    have hlt := pow_lt_pow_left₀ (lt_of_not_ge h) (pow_nonneg hypos.le 4)
      (by norm_num : (4 : ℕ) ≠ 0)
    have heq : (y ^ (4 : ℕ)) ^ (4 : ℕ) = N := by
      rw [← pow_mul]
      norm_num
      exact hy16
    rw [heq] at hlt
    norm_num at hlt
    norm_num at hNreal
    linarith
  have hfinal : 4800000 * (N : ℝ) * y ^ 12 ≤ (N : ℝ) ^ 2 := by
    calc _ ≤ y ^ 4 * (N : ℝ) * y ^ 12 := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right (by linarith : (4800000 : ℝ) ≤ y ^ 4) hNpos.le
          · positivity
      _ = (N : ℝ) ^ 2 := by rw [← hy16]; ring
  linarith

end Helfgott


open Finset ArithmeticFunction
open scoped BigOperators

namespace Helfgott

lemma triple_sum_of_mem {N : ℕ} {t : (ℕ × ℕ) × ℕ} (ht : t ∈ tripleIndices N) :
    t.1.1 + t.1.2 + t.2 = N :=
  (Finset.mem_filter.mp ht).2

theorem bad_weighted_triples_le (a b : ℕ → ℝ)
    (ha : ∀ n, |a n| ≤ (1079955 / 1000000 : ℝ))
    (hb : ∀ n, |b n| ≤ (707 / 500 : ℝ)) (N : ℕ) (hN : 10 ^ 27 ≤ N) :
    ∑ t ∈ badTripleIndices N, weightedTripleTerm a b t
      ≤ (1 / 5000 : ℝ) * (N : ℝ) ^ 2 := by
  classical
  let ppS : Finset ℕ := (Finset.range (N + 1)).filter
    (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)
  let badNums : Finset ℕ := insert 2 ppS
  let vm : ((ℕ × ℕ) × ℕ) → ℝ := fun t =>
    (vonMangoldt t.1.1 : ℝ) * (vonMangoldt t.1.2 : ℝ) * (vonMangoldt t.2 : ℝ)
  let B : Finset ((ℕ × ℕ) × ℕ) := (badTripleIndices N).filter (fun t => vm t ≠ 0)
  let T₁ := B.filter (fun t => t.1.1 ∈ badNums)
  let T₂ := B.filter (fun t => t.1.2 ∈ badNums)
  let T₃ := B.filter (fun t => t.2 ∈ badNums)
  have hBN {t} (ht : t ∈ B) : t ∈ tripleIndices N :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  have hvm {t} (ht : t ∈ B) :
      ((vonMangoldt t.1.1 : ℝ) ≠ 0 ∧ (vonMangoldt t.1.2 : ℝ) ≠ 0) ∧
        (vonMangoldt t.2 : ℝ) ≠ 0 := by
    simpa only [vm, mul_ne_zero_iff] using (Finset.mem_filter.mp ht).2
  have hbadnum (n : ℕ) (hn : n ≤ N) (hpp : IsPrimePow n) (hbad : ¬ IsOddPrime n) :
      n ∈ badNums := by
    by_cases hp : Nat.Prime n
    · have hn2 : n = 2 := by
        rcases hp.eq_two_or_odd' with hn2 | hodd
        · exact hn2
        · exact False.elim (hbad ⟨hp, hodd⟩)
      simp [badNums, hn2]
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp, hp⟩
  have hBbad (t) (ht : t ∈ B) :
      t.1.1 ∈ badNums ∨ t.1.2 ∈ badNums ∨ t.2 ∈ badNums := by
    have hsum := triple_sum_of_mem (hBN ht)
    have hv := hvm ht
    have hpp1 := vonMangoldt_ne_zero_iff.mp hv.1.1
    have hpp2 := vonMangoldt_ne_zero_iff.mp hv.1.2
    have hpp3 := vonMangoldt_ne_zero_iff.mp hv.2
    have hbad := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
    by_cases h1 : IsOddPrime t.1.1
    · by_cases h2 : IsOddPrime t.1.2
      · exact Or.inr (Or.inr (hbadnum _ (by omega) hpp3 (fun h3 => hbad ⟨h1, h2, h3⟩)))
      · exact Or.inr (Or.inl (hbadnum _ (by omega) hpp2 h2))
    · exact Or.inl (hbadnum _ (by omega) hpp1 h1)
  have hBT : B ⊆ (T₁ ∪ T₂) ∪ T₃ := by
    intro t ht
    rcases hBbad t ht with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, h⟩)
  have hT1card : T₁.card ≤ badNums.card * (N + 1) := by
    rw [← Finset.card_range (N + 1), ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun t => (t.1.1, t.1.2))
    · intro t ht
      have h := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
      have hs := triple_sum_of_mem (hBN h.1)
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨h.2,
        Finset.mem_range.mpr (by change t.1.2 < N + 1; omega)⟩)
    · intro t ht u hu heq
      have ht' := triple_sum_of_mem (hBN (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
      have hu' := triple_sum_of_mem (hBN (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).1)
      dsimp only at heq
      have hi : t.1.1 = u.1.1 := congrArg Prod.fst heq
      have hj : t.1.2 = u.1.2 := congrArg Prod.snd heq
      have hk : t.2 = u.2 := by omega
      exact Prod.ext (Prod.ext hi hj) hk
  have hT2card : T₂.card ≤ badNums.card * (N + 1) := by
    rw [← Finset.card_range (N + 1), ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun t => (t.1.2, t.2))
    · intro t ht
      have h := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
      have hs := triple_sum_of_mem (hBN h.1)
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨h.2,
        Finset.mem_range.mpr (by change t.2 < N + 1; omega)⟩)
    · intro t ht u hu heq
      have ht' := triple_sum_of_mem (hBN (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
      have hu' := triple_sum_of_mem (hBN (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).1)
      dsimp only at heq
      have hj : t.1.2 = u.1.2 := congrArg Prod.fst heq
      have hk : t.2 = u.2 := congrArg (fun z : ℕ × ℕ => z.2) heq
      have hi : t.1.1 = u.1.1 := by omega
      exact Prod.ext (Prod.ext hi hj) hk
  have hT3card : T₃.card ≤ badNums.card * (N + 1) := by
    rw [← Finset.card_range (N + 1), ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun t => (t.2, t.1.1))
    · intro t ht
      have h := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
      have hs := triple_sum_of_mem (hBN h.1)
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨h.2,
        Finset.mem_range.mpr (by change t.1.1 < N + 1; omega)⟩)
    · intro t ht u hu heq
      have ht' := triple_sum_of_mem (hBN (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1)
      have hu' := triple_sum_of_mem (hBN (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).1)
      dsimp only at heq
      have hk : t.2 = u.2 := congrArg Prod.fst heq
      have hi : t.1.1 = u.1.1 := congrArg Prod.snd heq
      have hj : t.1.2 = u.1.2 := by omega
      exact Prod.ext (Prod.ext hi hj) hk
  have hcard : B.card ≤ 3 * (ppS.card + 1) * (N + 1) := by
    have hbadcard : badNums.card ≤ ppS.card + 1 := Finset.card_insert_le _ _
    calc B.card ≤ ((T₁ ∪ T₂) ∪ T₃).card := Finset.card_le_card hBT
      _ ≤ (T₁.card + T₂.card) + T₃.card :=
        le_trans (Finset.card_union_le _ _)
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ 3 * badNums.card * (N + 1) := by nlinarith
      _ ≤ 3 * (ppS.card + 1) * (N + 1) := by gcongr
  have hcard' : B.card ≤ 3 * ((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1) * (N + 1) := by
    have hppcard := proper_prime_power_card N
    exact le_trans hcard (by gcongr)
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hterm : ∀ t ∈ B, weightedTripleTerm a b t ≤ 2 * Real.log (N : ℝ) ^ 3 := by
    intro t ht
    have hs := triple_sum_of_mem (hBN ht)
    have hv := hvm ht
    have hvmBound (n : ℕ) (hn : n ≤ N) (hne : (vonMangoldt n : ℝ) ≠ 0) :
        (vonMangoldt n : ℝ) ≤ Real.log (N : ℝ) := by
      have hnpos := (vonMangoldt_ne_zero_iff.mp hne).pos
      exact le_trans vonMangoldt_le_log
        (Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hn))
    have h1 := hvmBound _ (by omega) hv.1.1
    have h2 := hvmBound _ (by omega) hv.1.2
    have h3 := hvmBound _ (by omega) hv.2
    have h0 (n : ℕ) : (0 : ℝ) ≤ vonMangoldt n := vonMangoldt_nonneg
    have hprod : vm t ≤ Real.log (N : ℝ) ^ 3 := by
      calc vm t ≤ Real.log (N : ℝ) * Real.log (N : ℝ) * Real.log (N : ℝ) :=
            mul_le_mul (mul_le_mul h1 h2 (h0 _) hL0) h3 (h0 _) (mul_nonneg hL0 hL0)
        _ = _ := by ring
    have hw : |a t.1.1 * a t.1.2 * b t.2| ≤ 2 := by
      simp only [abs_mul]
      calc _ ≤ (1079955 / 1000000 : ℝ) * (1079955 / 1000000 : ℝ) * (707 / 500 : ℝ) :=
            mul_le_mul (mul_le_mul (ha _) (ha _) (abs_nonneg _) (by norm_num))
              (hb _) (abs_nonneg _) (by norm_num)
        _ ≤ 2 := by norm_num
    calc weightedTripleTerm a b t ≤ |weightedTripleTerm a b t| := le_abs_self _
      _ = vm t * |a t.1.1 * a t.1.2 * b t.2| := by
        change |vm t * (a t.1.1 * a t.1.2 * b t.2)| = _
        rw [abs_mul, abs_of_nonneg (by dsimp [vm]; positivity)]
      _ ≤ Real.log (N : ℝ) ^ 3 * 2 := mul_le_mul hprod hw (abs_nonneg _) (pow_nonneg hL0 _)
      _ = _ := by ring
  have hsumB : (∑ t ∈ badTripleIndices N, weightedTripleTerm a b t) =
      ∑ t ∈ B, weightedTripleTerm a b t := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro t ht hnot
    have hzero : vm t = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨ht, hne⟩)
    change vm t * (a t.1.1 * a t.1.2 * b t.2) = 0
    rw [hzero, zero_mul]
  rw [hsumB]
  calc _ ≤ (B.card : ℝ) * (2 * Real.log (N : ℝ) ^ 3) := by
        calc _ ≤ ∑ _ ∈ B, 2 * Real.log (N : ℝ) ^ 3 := Finset.sum_le_sum hterm
          _ = _ := by simp
    _ ≤ (3 * ((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1) * (N + 1) : ℕ) *
        (2 * Real.log (N : ℝ) ^ 3) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard'
      · positivity
    _ = 2 * 3 * (((Nat.sqrt N + 1) * (Nat.log 2 N + 1) + 1 : ℕ) : ℝ) *
        ((N + 1 : ℕ) : ℝ) * Real.log (N : ℝ) ^ 3 := by push_cast; ring
    _ ≤ _ := prime_power_error_small N hN

theorem three_odd_primes_of_weighted_count (a b : ℕ → ℝ)
    (ha : ∀ n, |a n| ≤ (1079955 / 1000000 : ℝ))
    (hb : ∀ n, |b n| ≤ (707 / 500 : ℝ)) (N : ℕ) (hN : 10 ^ 27 ≤ N)
    (hcount : (1 / 2500 : ℝ) * (N : ℝ) ^ 2 ≤
      ∑ t ∈ tripleIndices N, weightedTripleTerm a b t) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ N = p + q + r := by
  classical
  have hbad := bad_weighted_triples_le a b ha hb N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hgap : (∑ t ∈ badTripleIndices N, weightedTripleTerm a b t) <
      ∑ t ∈ tripleIndices N, weightedTripleTerm a b t := by
    have hsq : (0 : ℝ) < (N : ℝ) ^ 2 := sq_pos_of_pos hNpos
    nlinarith
  by_contra hnone
  have hsets : badTripleIndices N = tripleIndices N := by
    apply Finset.ext
    intro t
    simp only [badTripleIndices, Finset.mem_filter]
    constructor
    · exact fun ht => ht.1
    · intro ht
      refine ⟨ht, ?_⟩
      intro hgood
      have hsum := triple_sum_of_mem ht
      exact hnone ⟨t.1.1, t.1.2, t.2, hgood.1.1, hgood.2.1.1, hgood.2.2.1,
        hgood.1.2, hgood.2.1.2, hgood.2.2.2, hsum.symm⟩
  rw [hsets] at hgap
  exact (lt_irrefl _ hgap)

end Helfgott

theorem solution (a b : ℕ → ℝ)
    (ha : ∀ n, |a n| ≤ (1079955 / 1000000 : ℝ))
    (hb : ∀ n, |b n| ≤ (707 / 500 : ℝ)) (N : ℕ) (hN : 10 ^ 27 ≤ N)
    (hcount : (1 / 2500 : ℝ) * (N : ℝ) ^ 2 ≤
      ∑ t ∈ Helfgott.tripleIndices N, Helfgott.weightedTripleTerm a b t) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ N = p + q + r :=
  Helfgott.three_odd_primes_of_weighted_count a b ha hb N hN hcount

#print axioms solution
