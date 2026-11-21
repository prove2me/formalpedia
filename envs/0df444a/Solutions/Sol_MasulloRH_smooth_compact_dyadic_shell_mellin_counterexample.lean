-- Prove2me | solution 1 for MasulloRH.smooth_compact_dyadic_shell_mellin_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:41:20.869882+00:00
-- url     : https://prove2.me/submissions/b24dfdbb-af37-4ed6-aef5-5656166a5d3a

import Theorems.Thm_MasulloRH_corrected_prime_shell_mellin_limits
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.MellinTransform
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
section

open Finset
open scoped Classical

namespace MasulloSieve

def Survives (p B n : ℕ) : Prop :=
  p ∣ n ∧ ∀ q ≤ B, q.Prime → q ≠ p → ¬q ∣ n

theorem survives_iff_prime_power {p B n : ℕ} (hp : p.Prime) (hn : 0 < n) (hnB : n ≤ B) :
    Survives p B n ↔ ∃ j : ℕ, 0 < j ∧ n = p ^ j := by
  constructor
  · rintro ⟨hpn, hs⟩
    have heq := Nat.eq_prime_pow_of_unique_prime_dvd (p := p) hn.ne' (fun {q} hq hqn ↦ by
      by_contra hne
      exact hs q ((Nat.le_of_dvd hn hqn).trans hnB) hq hne hqn)
    refine ⟨_, Nat.pos_of_ne_zero (fun hzero ↦ hp.not_dvd_one ?_), heq⟩
    have hn1 : n = 1 := heq.trans (by rw [hzero, pow_zero])
    simpa only [hn1] using hpn
  · rintro ⟨j, hj, rfl⟩
    exact ⟨dvd_pow_self _ hj.ne', fun q _ hq hne hqd ↦
      hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqd))⟩

theorem sum_surviving_eq_sum_prime_powers {A : Type*} [AddCommMonoid A]
    {p N B : ℕ} (hp : p.Prime) (hNB : N ≤ B) (f : ℕ → A) :
    ∑ n ∈ (Icc 1 N).filter (Survives p B), f n =
      ∑ j ∈ (Icc 1 N).filter (fun j ↦ p ^ j ≤ N), f (p ^ j) := by
  symm
  apply sum_bij (fun j _ ↦ p ^ j)
  · intro j hj
    obtain ⟨hj, hjN⟩ := mem_filter.mp hj
    have hpos : 0 < p ^ j := Nat.pow_pos hp.pos
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos, hjN⟩,
      (survives_iff_prime_power hp hpos (hjN.trans hNB)).mpr ⟨j, (mem_Icc.mp hj).1, rfl⟩⟩
  · intro j _ k _ h
    exact Nat.pow_right_injective hp.two_le h
  · intro n hn
    obtain ⟨hn, hs⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := mem_Icc.mp hn
    obtain ⟨j, hj, rfl⟩ := (survives_iff_prime_power hp hnpos (hnN.trans hNB)).mp hs
    exact ⟨j, mem_filter.mpr ⟨mem_Icc.mpr ⟨hj, (Nat.lt_pow_self hp.one_lt).le.trans hnN⟩, hnN⟩, rfl⟩
  · intro _ _
    rfl

private theorem multiple_sum (d N : ℕ) (hd : 0 < d) (f : ℕ → ℂ) :
    ∑ m ∈ Icc 1 (N / d), f (d*m) =
      ∑ n ∈ Icc 1 N, if d ∣ n then f n else 0 := by
  rw [← sum_filter]
  apply sum_bij (fun m _ ↦ d*m)
  · intro m hm
    obtain ⟨hm0, hmN⟩ := mem_Icc.mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hm0, by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hmN⟩, dvd_mul_right _ _⟩
  · intro m _ k _ he
    exact Nat.mul_left_cancel hd he
  · intro n hn
    obtain ⟨hn, m, rfl⟩ := mem_filter.mp hn
    obtain ⟨hm0, hmN⟩ := mem_Icc.mp hn
    refine ⟨m, mem_Icc.mpr ⟨?_, (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hmN)⟩, rfl⟩
    exact Nat.pos_of_ne_zero (fun h ↦ by simp [h] at hm0)
  · intro _ _
    rfl

private theorem product_dvd_iff {n : ℕ} (hn : 0 < n) (U : Finset ℕ)
    (hU : ∀ q ∈ U, q.Prime ∧ q ≠ 2) :
    2 * ∏ q ∈ U, q ∣ n ↔ 2 ∣ n ∧ ∀ q ∈ U, q ∣ n := by
  have h2 : 2 ∉ U := fun h ↦ (hU 2 h).2 rfl
  rw [← prod_insert h2 (f := fun q : ℕ ↦ q)]
  constructor
  · intro h
    exact ⟨(dvd_prod_of_mem id (mem_insert_self 2 U)).trans h,
      fun q hq ↦ (dvd_prod_of_mem id (mem_insert_of_mem hq)).trans h⟩
  · rintro ⟨he, hall⟩
    apply dvd_trans _ (Nat.prod_primeFactors_dvd n)
    apply prod_dvd_prod_of_subset _ _ id
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, he, hn.ne'⟩
    · exact Nat.mem_primeFactors.mpr ⟨(hU q hq).1, hall q hq, hn.ne'⟩

private theorem exclusion_weight (Q : Finset ℕ) (n : ℕ) :
    (∑ U ∈ Q.powerset, (-1 : ℂ)^U.card * (if ∀ q ∈ U, q ∣ n then 1 else 0)) =
      if ∀ q ∈ Q, ¬q ∣ n then 1 else 0 := by
  let w (q : ℕ) : ℂ := if q ∣ n then 1 else 0
  have hwm (U : Finset ℕ) : (∏ q ∈ U, w q) = (if ∀ q ∈ U, q ∣ n then 1 else 0) := by
    simp [w, prod_ite_zero]
  have hpm (q : ℕ) : 1 - w q = if ¬q ∣ n then 1 else 0 := by by_cases h : q ∣ n <;> simp [w, h]
  have h := prod_sub (fun _ : ℕ ↦ (1 : ℂ)) w Q
  simp only [hpm, hwm, prod_const_one, mul_one, prod_ite_zero] at h
  exact h.symm

def oddPrimesThrough (B : ℕ) : Finset ℕ :=
  (range (B+1)).filter (fun q ↦ q.Prime ∧ q ≠ 2)

theorem finite_sieve_indicator {N B : ℕ} (hNB : N ≤ B) (f : ℕ → ℂ) :
    (∑ U ∈ (oddPrimesThrough B).powerset, (-1 : ℂ)^U.card *
      ∑ m ∈ Icc 1 (N / (2 * ∏ q ∈ U, q)), f ((2 * ∏ q ∈ U, q) * m)) =
    ∑ j ∈ (Icc 1 N).filter (fun j ↦ 2 ^ j ≤ N), f (2 ^ j) := by
  let Q := oddPrimesThrough B
  have hQ {q : ℕ} : q ∈ Q ↔ q ≤ B ∧ q.Prime ∧ q ≠ 2 := by simp [Q, oddPrimesThrough]
  have hU (U : Finset ℕ) (hu : U ∈ Q.powerset) (q : ℕ) (hq : q ∈ U) : q.Prime ∧ q ≠ 2 :=
    (hQ.mp (mem_powerset.mp hu hq)).2
  rw [← sum_surviving_eq_sum_prime_powers Nat.prime_two hNB, sum_filter]
  change (∑ U ∈ Q.powerset, _) = _
  calc
    _ = ∑ U ∈ Q.powerset, ∑ n ∈ Icc 1 N, (-1 : ℂ)^U.card *
          (if 2 * ∏ q ∈ U, q ∣ n then f n else 0) := by
      apply sum_congr rfl
      intro U hu
      rw [multiple_sum _ _ (Nat.mul_pos (by decide) (prod_pos fun q hq ↦ (hU U hu q hq).1.pos)), mul_sum]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      have hnp := (mem_Icc.mp hn).1
      by_cases he : 2 ∣ n
      · have hrew (U : Finset ℕ) (hu : U ∈ Q.powerset) :
            (-1 : ℂ)^U.card * (if 2 * ∏ q ∈ U, q ∣ n then f n else 0) =
              ((-1 : ℂ)^U.card * (if ∀ q ∈ U, q ∣ n then 1 else 0)) * f n := by
          by_cases h : ∀ q ∈ U, q ∣ n <;> simp [product_dvd_iff hnp U (hU U hu), he, h]
        rw [sum_congr rfl hrew, ← sum_mul, exclusion_weight]
        have hs : (∀ q ∈ Q, ¬q ∣ n) ↔ Survives 2 B n := by
          constructor
          · exact fun h ↦ ⟨he, fun q hq hP hne ↦ h q (hQ.mpr ⟨hq, hP, hne⟩)⟩
          · exact fun h q hq ↦ h.2 q (hQ.mp hq).1 (hQ.mp hq).2.1 (hQ.mp hq).2.2
        by_cases h : Survives 2 B n <;> simp [hs, h]
      · have hs : ¬Survives 2 B n := fun h ↦ he h.1
        rw [if_neg hs]
        apply sum_eq_zero
        intro U hu
        simp [product_dvd_iff hnp U (hU U hu), he]

theorem finite_sieve_indicator_range {N B : ℕ} (hNB : N ≤ B) (f : ℕ → ℂ) (hf : f 0 = 0) :
    (∑ U ∈ (oddPrimesThrough B).powerset, (-1 : ℂ)^U.card *
      ∑ m ∈ range (N / (2 * ∏ q ∈ U, q) + 1), f ((2 * ∏ q ∈ U, q) * m)) =
    ∑ j ∈ (Icc 1 N).filter (fun j ↦ 2 ^ j ≤ N), f (2 ^ j) := by
  rw [← finite_sieve_indicator hNB f]
  apply sum_congr rfl
  intro U _
  have hset (k : ℕ) : range (k+1) = insert 0 (Icc 1 k) := by
    ext m
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp)]
  simp [hf]

end MasulloSieve


open Finset Filter

private lemma lattice_cutoff (f : ℕ → ℂ) (N c : ℕ) (hc : 0 < c)
    (hvan : ∀ n, N < n → f n = 0) :
    (∑' j : ℕ, f (c*(j+1))) = ∑ m ∈ Icc 1 (N/c), f (c*m) := by
  have ht (j : ℕ) (hj : j ∉ range (N/c)) : f (c*(j+1)) = 0 := by
    simp only [mem_range,not_lt] at hj
    apply hvan
    rw [mul_comm]
    exact (Nat.div_lt_iff_lt_mul hc).mp (by omega)
  rw [tsum_eq_sum ht]
  refine sum_bij' (fun j _ => j+1) (fun m _ => m-1) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [mem_range] at hj; exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro m hm; obtain ⟨h1,h2⟩ := mem_Icc.mp hm; apply mem_range.mpr; omega
  · intro _ _; omega
  · intro m hm; have := (mem_Icc.mp hm).1; omega
  · intro _ _; rfl

private lemma dyadic_cutoff (f : ℕ → ℂ) (N : ℕ) (hvan : ∀ n, N < n → f n = 0) :
    (∑ j ∈ (Icc 1 N).filter (fun j => 2^j≤N), f (2^j)) = ∑' j : ℕ, f (2^(j+1)) := by
  have ht (j : ℕ) (hj : j ∉ range N) : f (2^(j+1)) = 0 := by
    simp only [mem_range,not_lt] at hj
    apply hvan
    exact lt_of_le_of_lt hj ((Nat.lt_succ_self j).trans (show j+1 < 2^(j+1) from Nat.lt_two_pow_self))
  rw [tsum_eq_sum ht, sum_filter]
  calc
      _ = ∑ j ∈ Icc 1 N, f (2^j) := by
        apply sum_congr rfl
        intro j _
        split_ifs with h
        · rfl
        · rw [hvan _ (lt_of_not_ge h)]
      _ = _ := by
        symm; refine sum_bij' (fun j _ => j+1) (fun m _ => m-1) ?_ ?_ ?_ ?_ ?_
        · intro j hj; simp only [mem_range] at hj; exact mem_Icc.mpr ⟨by omega,by omega⟩
        · intro m hm; obtain ⟨h1,h2⟩ := mem_Icc.mp hm; apply mem_range.mpr; omega
        · intro _ _; omega
        · intro m hm; have := (mem_Icc.mp hm).1; omega
        · intro _ _; rfl
private theorem dyadic_halfline_stabilization (ψ : ℝ → ℂ) (R : ℝ)
    (hcut : ∀ y : ℝ, R ≤ y → ψ y = 0) :
    let F (t : ℝ) := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)
    let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2)
    let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
      (-1:ℂ)^U.card * F ((2*∏ l ∈ U,(l:ℝ))*t)
    ∀ a : ℝ, 0 < a → ∀ᶠ B : ℕ in atTop, ∀ t : ℝ, a ≤ t →
        G B t = ∑' j : ℕ, ψ (2^(j+1)*t) := by
  intro F Q G a ha
  obtain ⟨N,hN⟩ := exists_nat_ge (R/a)
  filter_upwards [eventually_ge_atTop N] with B hB
  intro t ht
  let f (n : ℕ) := ψ ((n:ℝ)*t)
  have hvan (n : ℕ) (hn : N<n) : f n = 0 := by
    apply hcut
    have hna : R ≤ (N:ℝ)*a := (div_le_iff₀ ha).mp hN
    exact hna.trans (mul_le_mul (by exact_mod_cast hn.le) ht ha.le (Nat.cast_nonneg _))
  have hU (U : Finset ℕ) (hU : U ∈ (Q B).powerset) :
      F ((2*∏ l ∈ U,(l:ℝ))*t) = ∑ m ∈ Icc 1 (N/(2*∏ l ∈ U,l)), f ((2*∏ l ∈ U,l)*m) := by
    let c : ℕ := 2*∏ l ∈ U,l
    have hc : 0<c := Nat.mul_pos (by decide) (Finset.prod_pos fun l hl => (mem_filter.mp (mem_powerset.mp hU hl)).2.1.pos)
    rw [←lattice_cutoff f N c hc hvan]
    apply tsum_congr
    intro j
    change ψ (((j:ℝ)+1)*((2*(∏ l ∈ U,(l:ℝ)))*t)) = ψ (((c*(j+1):ℕ):ℝ)*t)
    congr 1
    dsimp [c]
    push_cast
    ring
  calc
    G B t = ∑ U ∈ (Q B).powerset, (-1:ℂ)^U.card *
        ∑ m ∈ Icc 1 (N/(2*∏ l ∈ U,l)), f ((2*∏ l ∈ U,l)*m) := by
      apply sum_congr rfl
      intro U h
      rw [hU U h]
    _ = ∑ j ∈ (Icc 1 N).filter (fun j => 2^j≤N), f (2^j) :=
      MasulloSieve.finite_sieve_indicator hB f
    _ = ∑' j : ℕ, f (2^(j+1)) := dyadic_cutoff f N hvan
    _ = _ := by simp [f]
end

section

namespace MasulloRH

theorem exists_bound_iteratedDerivWithin_two {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, a < b → ∀ x : ℝ,
      |iteratedDerivWithin 2 ψ (Set.uIcc a b) x| ≤ M := by
  have hd : HasCompactSupport (iteratedDeriv 2 ψ) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc.deriv.deriv
  obtain ⟨M, hM⟩ := (ContDiff.continuous_iteratedDeriv' 2 hψ).bounded_above_of_compact_support hd
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM₀, fun a b hab x ↦ ?_⟩
  rw [Set.uIcc_of_le hab.le]
  by_cases hx : x ∈ Set.Icc a b
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hψ.contDiffAt hx]
    exact hM x
  · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
      (by rwa [closure_Icc]), abs_zero]
    exact hM₀

end MasulloRH

open MeasureTheory Set Filter
open scoped Topology

noncomputable def sieveLattice (ψ : ℝ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, ψ (((n:ℝ)+1)*t)

private theorem sieve_trap_bound (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (R : ℝ) (hR : 0<R)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0) (hmean : (∫ x : ℝ, ψ x) = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ b : ℝ, 0 < b → ∀ x : ℝ, |iteratedDerivWithin 2 ψ (uIcc 0 b) x| ≤ M)
    (t : ℝ) (ht : 0<t) : |sieveLattice ψ t| ≤ M*(R+t)*t/12 := by
  let N : ℕ := ⌈R/t⌉₊
  have hN : 0<N := Nat.ceil_pos.mpr (div_pos hR ht)
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hn0 := hn.ne'
  have hNt : R ≤ (N:ℝ)*t := (div_le_iff₀ ht).mp (Nat.le_ceil _)
  have hNt' : (N:ℝ)*t < R+t := by
    have hc : (N:ℝ) < R/t+1 := Nat.ceil_lt_add_one (div_nonneg hR.le ht.le)
    calc
      _ < (R/t+1)*t := (mul_lt_mul_of_pos_right hc ht)
      _ = _ := by field_simp
  have hb : 0 < (N:ℝ)*t := mul_pos hn ht
  have hsum : sieveLattice ψ t = ∑ k ∈ Finset.range (N-1), ψ (((k:ℝ)+1)*t) := by
    apply tsum_eq_sum
    intro n hn'
    apply hvan
    right
    apply hNt.trans
    apply mul_le_mul_of_nonneg_right _ ht.le
    have : N ≤ n+1 := by have := mt Finset.mem_range.mpr hn'; omega
    exact_mod_cast this
  have hint : (∫ x in (0:ℝ)..((N:ℝ)*t), ψ x) = 0 := by
    rw [intervalIntegral.integral_of_le hb.le, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hmean
    · intro x hx
      apply hvan
      by_cases hp : 0<x
      · right
        exact hNt.trans (by by_contra! h'; exact hx ⟨hp,h'.le⟩)
      · exact Or.inl (le_of_not_gt hp)
  have htr : trapezoidal_integral ψ N 0 ((N:ℝ)*t) = t*sieveLattice ψ t := by
    unfold trapezoidal_integral
    rw [hvan 0 (Or.inl le_rfl),hvan _ (Or.inr hNt),hsum]
    simp only [sub_zero, add_zero, zero_div, zero_add]
    have hratio : (N:ℝ)*t/N=t := by field_simp
    rw [hratio]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    field_simp
  have he := trapezoidal_error_le_of_c2 (a:=0) (b:=(N:ℝ)*t)
    hψ.contDiffOn (hder _ hb) hN
  rw [trapezoidal_error,htr,hint,sub_zero,abs_mul,abs_of_pos ht,sub_zero,abs_of_pos hb] at he
  have hr : ((N:ℝ)*t)^3*M/(12*(N:ℝ)^2) = ((N:ℝ)*t)*M*t^2/12 := by field_simp
  rw [hr] at he
  have htdiv : t*|sieveLattice ψ t| ≤ t*(M*(R+t)*t/12) := by
    apply he.trans
    have hcmp := mul_le_mul_of_nonneg_right hNt'.le (mul_nonneg hM (sq_nonneg t))
    linarith only [show ((N:ℝ)*t)*M*t^2 ≤ M*(R+t)*t*t by linarith only [hcmp]]
  exact le_of_mul_le_mul_left htdiv ht

private lemma sieve_measurable (ψ : ℝ → ℝ) (hψ : Continuous ψ) : Measurable (sieveLattice ψ) := by
  apply Measurable.tsum
  intro n
  exact (hψ.comp (continuous_const.mul continuous_id)).measurable

private lemma sieve_vanishes (ψ : ℝ → ℝ) (R : ℝ) (hR : 0<R)
    (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0) (t : ℝ) (ht : R≤t) :
    sieveLattice ψ t = 0 := by
  unfold sieveLattice
  convert tsum_zero (α:=ℝ) (β:=ℕ) using 1
  congr
  funext n
  apply hvan _ ∘ Or.inr
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn ((hR.le.trans ht))]

private lemma sieve_log_of_bound (F : ℝ → ℝ) (hm : Measurable F) (R C : ℝ)
    (hbound : ∀ t, 0<t → t≤R → |F t| ≤ C*t) (hzero : ∀ t, R≤t → F t=0) :
    IntegrableOn (fun t : ℝ => F t/t) (Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ => F t/t) := hm.div measurable_id
  have hnear : IntegrableOn (fun t : ℝ => F t/t) (Ioc 0 R) := by
    apply (integrableOn_const (μ:=volume) (s:=Ioc 0 R) (C:=C) (by simp [Real.volume_Ioc])).mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs,abs_div,abs_of_pos ht.1]
    exact (div_le_iff₀ ht.1).mpr (hbound t ht.1 ht.2)
  have hfar : IntegrableOn (fun t : ℝ => F t/t) (Ioi R) := by
    have he : EqOn (fun t : ℝ => F t/t) (fun _ => 0) (Ioi R) := by
      intro t ht; simp [hzero t (le_of_lt ht)]
    exact (integrableOn_congr_fun he measurableSet_Ioi).mpr (by simp)
  apply (hnear.union hfar).mono_set
  intro t ht
  by_cases h : t≤R
  · exact Or.inl ⟨ht,h⟩
  · exact Or.inr (lt_of_not_ge h)

open Complex Set MeasureTheory

theorem sieve_mellin_of_bound (F : ℝ → ℝ) (hm : Measurable F) (R C : ℝ) (hR : 0<R)
    (hC : 0≤C) (hsmall : ∀ t, 0<t → t≤R → |F t|≤C*t)
    (hzero : ∀ t, R≤t → F t=0) (s : ℂ) (hs : 0≤s.re) :
    MellinConvergent (fun t => (F t:ℂ)) s := by
  let M := C * R^s.re
  have hM : 0 ≤ M := mul_nonneg hC (Real.rpow_nonneg hR.le _)
  have hi : Integrable ((Ioo 0 R).indicator (fun _ : ℝ => M)) := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const (ne_of_lt measure_Ioo_lt_top)
  change IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1) * (F t:ℂ)) (Ioi 0)
  apply hi.integrableOn.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi (0:ℝ)) measurableSet_Ioi] with t ht
  have ht0 : 0<t := ht
  by_cases h : t<R
  · rw [Set.indicator_of_mem (show t∈Ioo 0 R from ⟨ht0,h⟩)]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,Complex.norm_real,Real.norm_eq_abs,sub_re,one_re]
    have hpow : t^(s.re-1) * t = t^s.re := by
      conv_lhs => rhs; rw [← Real.rpow_one t]
      rw [←Real.rpow_add ht0]; congr 1; ring
    calc t^(s.re-1) * |F t| ≤ t^(s.re-1)*(C*t) :=
          mul_le_mul_of_nonneg_left (hsmall t ht0 h.le) (Real.rpow_nonneg ht0.le _)
         _ = C*t^s.re := by rw [← hpow]; ring
         _ ≤ M := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0.le h.le hs) hC
  · rw [Set.indicator_of_notMem (fun he : t ∈ Ioo 0 R => h he.2), hzero t (le_of_not_gt h)]
    simp

open Filter Set MeasureTheory Asymptotics
open scoped Topology

theorem MasulloRH.smooth_lattice_sum_mellin_convergence
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ) (hcomp : HasCompactSupport ψ)
    (R : ℝ) (hR : 0 < R) (hvan : ∀ x : ℝ, x ≤ 0 ∨ R ≤ x → ψ x = 0)
    (hmean : (∫ x in Ioi (0:ℝ), ψ x) = 0) :
    (fun t : ℝ => ∑' n : ℕ, ψ (((n:ℝ)+1)*t)) =O[𝓝[>] 0] (fun t : ℝ => t) ∧
    IntegrableOn (fun t : ℝ => (∑' n : ℕ, ψ (((n:ℝ)+1)*t)) / t) (Ioi 0) ∧
    ∀ s : ℂ, 0 ≤ s.re →
      MellinConvergent (fun t : ℝ => ((∑' n : ℕ, ψ (((n:ℝ)+1)*t)) : ℂ)) s := by
  obtain ⟨M,hM,hd⟩ := MasulloRH.exists_bound_iteratedDerivWithin_two hψ hcomp
  let C := M*(R+R)/12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmean' : (∫ x : ℝ, ψ x) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=Ioi (0:ℝ)) (f:=ψ)]
    · exact hmean
    · intro x hx; exact hvan x (Or.inl (le_of_not_gt hx))
  have hzero := sieve_vanishes ψ R hR hvan
  have hsmall (t : ℝ) (ht : 0<t) (hr : t≤R) : |sieveLattice ψ t| ≤ C*t := by
    apply (sieve_trap_bound ψ hψ R hR hvan hmean' M hM (hd 0) t ht).trans
    have hmul := mul_nonneg (mul_nonneg hM (sub_nonneg.mpr hr)) ht.le
    dsimp [C]
    nlinarith only [hmul]
  refine ⟨IsBigO.of_bound C ?_, sieve_log_of_bound _ (sieve_measurable ψ hψ.continuous) R C hsmall hzero, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0<t := ht
    change |sieveLattice ψ t| ≤ C*|t|
    rw [abs_of_pos ht']
    by_cases h : t ≤ R
    · exact hsmall t ht' h
    · rw [hzero t (le_of_not_ge h), abs_zero]; positivity
  · simpa only [sieveLattice, Complex.ofReal_tsum] using
      sieve_mellin_of_bound _ (sieve_measurable ψ hψ.continuous) R C hR hC hsmall hzero

end

section

open MeasureTheory Set

theorem MasulloRH.half_test_smooth_mean_zero (b : ℝ → ℝ) (hb : ContDiff ℝ 2 b)
    (hcompact : HasCompactSupport b) (hcut : ∀ t : ℝ, t ≤ 1 ∨ 2 ≤ t → b t = 0) :
    let g (t : ℝ) := b t - b (t/2)/2
    let ψ (t : ℝ) := g (t/2) - g t
    ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ (∀ t : ℝ, t ≤ 0 ∨ 8 ≤ t → ψ t = 0) ∧
    (∫ t in Ioi (0:ℝ), ψ t) = 0 ∧
    ∀ t : ℝ, 0 < t → Summable (fun n : ℕ => (ψ (((n:ℝ)+1)*t) : ℂ)) := by
  intro g ψ
  have hDg : ContDiff ℝ 2 g := by
    dsimp only [g]
    fun_prop
  have hDψ : ContDiff ℝ 2 ψ := by
    dsimp only [ψ]
    fun_prop
  have hg0 (t : ℝ) (h : t≤0 ∨ 4≤t) : g t = 0 := by
    dsimp only [g]
    rcases h with h|h
    · rw [hcut t (Or.inl (by linarith)), hcut (t/2) (Or.inl (by linarith))]
      norm_num
    · rw [hcut t (Or.inr (by linarith)), hcut (t/2) (Or.inr (by linarith))]
      norm_num
  have hp0 (t : ℝ) (h : t≤0 ∨ 8≤t) : ψ t = 0 := by
    dsimp only [ψ]
    rcases h with h|h
    · rw [hg0 t (Or.inl h), hg0 (t/2) (Or.inl (by linarith)), sub_self]
    · rw [hg0 t (Or.inr (by linarith)), hg0 (t/2) (Or.inr (by linarith)), sub_self]
  have hcψ : HasCompactSupport ψ := by
    apply HasCompactSupport.intro (K := Icc (0:ℝ) 8) isCompact_Icc
    intro x hx
    apply hp0
    by_cases h : x≤0
    · exact Or.inl h
    · right; by_contra! hh; exact hx ⟨le_of_not_ge h,hh.le⟩
  have scaled (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
      IntegrableOn (fun t : ℝ => f (t/2)) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), f (t/2)) = 2 * ∫ t in Ioi (0:ℝ), f t := by
    constructor
    · simpa only [one_div_mul_eq_div, mul_zero] using
        (integrableOn_Ioi_comp_mul_left_iff f 0 (show (0:ℝ)<1/2 by norm_num)).mpr (by simpa using hf)
    · simpa only [one_div_mul_eq_div, mul_zero, inv_div, div_one, smul_eq_mul] using
        integral_comp_mul_left_Ioi f 0 (show (0:ℝ)<1/2 by norm_num)
  have hbI : IntegrableOn b (Ioi 0) := (hb.continuous.integrable_of_hasCompactSupport hcompact).integrableOn
  obtain ⟨hb2,hbval⟩ := scaled b hbI
  have hgI : IntegrableOn g (Ioi 0) := hbI.sub (hb2.div_const 2)
  have hgmean : (∫ t in Ioi (0:ℝ), g t) = 0 := by
    change (∫ t in Ioi (0:ℝ), b t - b (t/2)/2) = 0
    rw [integral_sub hbI (hb2.div_const 2),integral_div,hbval]
    ring
  obtain ⟨hg2,hgval⟩ := scaled g hgI
  refine ⟨hDψ,hcψ,hp0,?_,?_⟩
  · change (∫ t in Ioi (0:ℝ), g (t/2)-g t) = 0
    rw [integral_sub hg2 hgI,hgval,hgmean]
    norm_num
  · intro t ht
    obtain ⟨N,hN⟩ := exists_nat_ge (8/t)
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    have hnN : N≤n := by simpa using hn
    have hn' : 8/t ≤ (n:ℝ)+1 := hN.trans (by exact_mod_cast (by omega : N≤n+1))
    rw [hp0 _ (Or.inr ((div_le_iff₀ ht).mp hn'))]
    simp
end

section

open Filter

theorem MasulloSieve.dyadic_difference_tsum (g : ℝ → ℝ) (R : ℝ)
    (hcut : ∀ x, R ≤ x → g x = 0) {t : ℝ} (ht : 0 < t) :
    (∑' j : ℕ, ((g ((2 : ℝ) ^ (j + 1) * t / 2) - g (2 ^ (j + 1) * t) : ℝ) : ℂ)) =
      (g t : ℂ) := by
  let u (j : ℕ) : ℂ := g (2 ^ j * t)
  have hlarge : Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ j * t) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const ht
  have hu : Summable u := by
    apply summable_zero.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hlarge.eventually_ge_atTop R] with j hj
    simp [u, hcut _ hj]
  have hhalf (j : ℕ) : (2 : ℝ) ^ (j + 1) * t / 2 = 2 ^ j * t := by rw [pow_succ]; ring
  simp_rw [hhalf, Complex.ofReal_sub]
  change (∑' j : ℕ, (u j - u (j + 1))) = _
  rw [hu.tsum_sub ((summable_nat_add_iff 1).mpr hu), hu.tsum_eq_zero_add, add_sub_cancel_right]
  simp [u]

end

section

open Set MeasureTheory

theorem MasulloAudit.exists_half_mellin_test_bump :
    ∃ b : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      tsupport b ⊆ Icc 1 2 ∧ (∀ t : ℝ, t ≤ 1 ∨ 2 ≤ t → b t = 0) ∧
      MellinConvergent (fun t => (b t : ℂ)) (1/2 : ℂ) ∧
      mellin (fun t => (b t : ℂ)) (1/2 : ℂ) ≠ 0 := by
  let φ : ContDiffBump (3/2 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  have hz (t : ℝ) (h : t ≤ 1 ∨ 2 ≤ t) : φ t = 0 := by
    apply φ.zero_of_le_dist
    change 1/4 ≤ dist t (3/2)
    rw [Real.dist_eq]
    rcases h with h | h
    · linarith [neg_le_abs (t-3/2)]
    · linarith [le_abs_self (t-3/2)]
  have hts : tsupport (fun t : ℝ => φ t) ⊆ Icc 1 2 := by
    rw [φ.tsupport_eq]
    intro t ht
    change dist t (3/2) ≤ 1/4 at ht
    rw [Real.dist_eq, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let w (t : ℝ) := (max t 1) ^ (-(1/2:ℝ))
  let g (t : ℝ) := w t * φ t
  have hmax (t : ℝ) : 0 < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hw : Continuous w :=
    (continuous_id.max continuous_const).rpow_const fun t => Or.inl (hmax t).ne'
  have hg : Continuous g := hw.mul φ.continuous
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mul_left (f:=w)
  have hg0 (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.rpow_nonneg (hmax t).le _) φ.nonneg
  have hcenter : φ (3/2) = 1 :=
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
  have hgp : 0 < ∫ t : ℝ, g t := by
    apply hg.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc hg0 (x := (3/2:ℝ))
    simp only [g, hcenter, mul_one]
    exact (Real.rpow_pos_of_pos (hmax _) _).ne'
  have he : (1/2 : ℂ)-1 = ((-(1/2:ℝ) : ℝ) : ℂ) := by norm_num
  have hc : EqOn (fun t : ℝ => (t : ℂ) ^ ((1/2:ℂ)-1) • (φ t : ℂ))
      (fun t => (g t : ℂ)) (Ioi 0) := by
    intro t ht
    by_cases h : t ≤ 1
    · simp [g, hz t (Or.inl h)]
    · simp only [smul_eq_mul, g, w, max_eq_left (le_of_not_ge h), Complex.ofReal_mul,
        Complex.ofReal_cpow (le_of_lt ht), he]
  have hgp' : (∫ t in Ioi (0:ℝ), g t) = ∫ t, g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro t ht
      have ht' : t ≤ 0 := le_of_not_gt ht
      simp [g, hz t (Or.inl (by linarith))])
  refine ⟨φ,φ.contDiff,φ.hasCompactSupport,hts,hz,?_,?_⟩
  · exact (integrableOn_congr_fun hc measurableSet_Ioi).mpr
      (hg.integrable_of_hasCompactSupport hgc).ofReal.integrableOn
  · unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hc]
    have hr : (∫ t in Ioi (0:ℝ), (g t:ℂ)) = Complex.ofReal (∫ t in Ioi (0:ℝ), g t) :=
      integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0:ℝ))) (f := g)
    rw [hr, hgp']
    exact Complex.ofReal_ne_zero.mpr hgp.ne'
end

section

namespace MasulloRH

/-- Two dyadic differences preserve nonvanishing of the half-weight Mellin moment. -/
theorem half_wavelet_mellin_ne_zero {b : ℝ → ℝ}
    (hb : MellinConvergent (fun t ↦ (b t : ℂ)) (1/2))
    (hb₀ : mellin (fun t ↦ (b t : ℂ)) (1/2) ≠ 0) :
    let g : ℝ → ℝ := fun t ↦ b t - b (t/2)/2
    let ψ : ℝ → ℝ := fun t ↦ g (t/2) - g t
    MellinConvergent (fun t ↦ (ψ t : ℂ)) (1/2) ∧ mellin (fun t ↦ (ψ t : ℂ)) (1/2) ≠ 0 := by
  let k : ℂ := (1/2 : ℂ) ^ (-(1/2 : ℂ))
  have hk : k * k = 2 := by
    dsimp [k]
    rw [← Complex.cpow_add _ _ (by norm_num)]
    norm_num [Complex.cpow_neg]
  have hscale (f : ℝ → ℂ) (hf : MellinConvergent f (1/2)) :
      HasMellin (fun t ↦ f (t/2)) (1/2) (k * mellin f (1/2)) := by
    have hh : 0 < (1/2 : ℝ) := by norm_num
    have he (t : ℝ) : 1/2*t = t/2 := by ring
    refine ⟨?_, ?_⟩
    · simpa only [he] using (MellinConvergent.comp_mul_left hh).mpr hf
    · simpa only [he, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, smul_eq_mul, k]
        using mellin_comp_mul_left f (1/2) hh
  let g : ℝ → ℝ := fun t ↦ b t - b (t/2)/2
  have hB := hscale (fun t ↦ (b t : ℂ)) hb
  have hG : HasMellin (fun t ↦ (g t : ℂ)) (1/2) ((1-k/2) * mellin (fun t ↦ (b t : ℂ)) (1/2)) := by
    have hd := hasMellin_sub hb (hB.1.div_const 2)
    have he (t : ℝ) : (g t : ℂ) = (b t : ℂ) - (b (t/2) : ℂ)/2 := by
      simp [g]
    simp_rw [he]
    refine ⟨hd.1, hd.2.trans ?_⟩
    rw [mellin_div_const, hB.2]
    ring
  have hD := hscale (fun t ↦ (g t : ℂ)) hG.1
  have hW := hasMellin_sub hD.1 hG.1
  change MellinConvergent (fun t ↦ ((g (t/2) - g t : ℝ) : ℂ)) (1/2) ∧
    mellin (fun t ↦ ((g (t/2) - g t : ℝ) : ℂ)) (1/2) ≠ 0
  simp only [Complex.ofReal_sub]
  refine ⟨hW.1, ?_⟩
  rw [hW.2, hD.2, ← sub_one_mul, hG.2]
  apply mul_ne_zero _ (mul_ne_zero _ hb₀)
  · intro hk₁
    have : k = 1 := sub_eq_zero.mp hk₁
    rw [this] at hk
    norm_num at hk
  · intro hz
    have hk₂ : k = 2 := by linear_combination -2 * hz
    rw [hk₂] at hk
    norm_num at hk

end MasulloRH

end

section
open Finset Filter Set MeasureTheory
open scoped Topology

theorem solution :
    ∃ ψ g : ℝ → ℝ,
      let F (t : ℝ) : ℂ := ∑' n : ℕ, (ψ (((n:ℝ)+1)*t) : ℂ)
      let Q (B : ℕ) := (range (B+1)).filter (fun l : ℕ => l.Prime ∧ l ≠ 2)
      let G (B : ℕ) (t : ℝ) := ∑ U ∈ (Q B).powerset,
        (-1:ℂ)^U.card * F ((2*∏ l ∈ U, (l:ℝ))*t)
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      (∀ t : ℝ, t ≤ 0 ∨ 8 ≤ t → ψ t = 0) ∧
      (∫ t in Ioi (0:ℝ), ψ t) = 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ t : ℝ, 0 < t → (∑' j : ℕ, (ψ (2^(j+1)*t):ℂ)) = (g t : ℂ)) ∧
      (∀ δ : ℝ, 0 < δ → ∀ᶠ B : ℕ in atTop, ∀ t : ℝ, δ ≤ t → G B t = (g t : ℂ)) ∧
      (∀ B : ℕ, MellinConvergent (G B) (1/2:ℂ)) ∧
      Tendsto (fun B : ℕ => mellin (G B) (1/2:ℂ)) atTop (𝓝 0) ∧
      MellinConvergent (fun t : ℝ => (g t : ℂ)) (1/2:ℂ) ∧
      mellin (fun t : ℝ => (g t : ℂ)) (1/2:ℂ) ≠ 0 := by
  obtain ⟨b,hb,hbc,_,hcut,hbm,hbn⟩ := MasulloAudit.exists_half_mellin_test_bump
  let g (t : ℝ) := b t - b (t/2)/2
  let ψ (t : ℝ) := g (t/2) - g t
  obtain ⟨hmψ, hmnψ⟩ := MasulloRH.half_wavelet_mellin_ne_zero hbm hbn
  obtain ⟨hC,hcomp,hvan,hmean,hsum⟩ := MasulloRH.half_test_smooth_mean_zero b
    (hb.of_le (show ((2:ℕ∞):WithTop ℕ∞) ≤ ((⊤:ℕ∞):WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)) hbc hcut
  have hCg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp only [g]; fun_prop
  have hCψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by dsimp only [ψ]; fun_prop
  have hgcut (t : ℝ) (ht : t ≤ 0 ∨ 4 ≤ t) : g t = 0 := by
    dsimp only [g]
    rcases ht with ht | ht
    · rw [hcut t (Or.inl (by linarith)), hcut _ (Or.inl (by linarith))]
      norm_num
    · rw [hcut t (Or.inr (by linarith)), hcut _ (Or.inr (by linarith))]
      norm_num
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.intro (K := Set.Icc (0:ℝ) 4) isCompact_Icc
    intro t ht
    apply hgcut
    by_cases h : t≤0
    · exact Or.inl h
    · right; by_contra! h'; exact ht ⟨le_of_not_ge h,h'.le⟩
  let ψC (t : ℝ) : ℂ := ψ t
  let shell (t : ℝ) := ∑' j : ℕ, ψC ((2:ℝ)^(j+1)*t)
  have heq (t : ℝ) (ht : 0<t) : shell t = (g t:ℂ) :=
    MasulloSieve.dyadic_difference_tsum g 4 (fun x hx => hgcut x (Or.inr hx)) ht
  have hF := (MasulloRH.smooth_lattice_sum_mellin_convergence ψ hC hcomp 8 (by norm_num)
      hvan hmean).2.2 (1/2:ℂ) (by norm_num)
  have generic := MasulloRH.corrected_prime_shell_mellin_limits 2 Nat.prime_two (1/2:ℝ)
    (by norm_num) (by norm_num) ψC (by simpa only [Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hmψ) ⟨hsum,by simpa [ψC, Complex.ofReal_tsum] using hF⟩
  simp only [Nat.cast_ofNat, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at generic
  obtain ⟨hfin,hlim,hM,hcontra⟩ := generic
  have heint : Set.EqOn (fun t : ℝ => (t:ℂ)^((1/2:ℂ)-1) • shell t)
        (fun t : ℝ => (t:ℂ)^((1/2:ℂ)-1) • (g t:ℂ)) (Ioi (0:ℝ)) :=
    fun t ht => congrArg _ (heq t ht)
  have heM : mellin shell (1/2:ℂ) = mellin (fun t : ℝ => (g t:ℂ)) (1/2:ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi heint
  have hvanC (t : ℝ) (ht : 8 ≤ t) : ψC t = 0 := by
    change (ψ t:ℂ)=0
    exact_mod_cast (show ψ t = 0 from hvan t (Or.inr ht))
  have hstab := dyadic_halfline_stabilization ψC 8 hvanC
  refine ⟨ψ,g,hCψ,hcomp,hvan,hmean,hCg,hgc,heq,?_,fun B => (hfin B).1,hlim,?_,?_⟩
  · intro δ hδ
    filter_upwards [hstab δ hδ] with B hB
    intro t ht
    exact (hB t ht).trans (heq t (hδ.trans_le ht))
  · exact (integrableOn_congr_fun heint measurableSet_Ioi).mp hM.1
  · intro hz
    have hzS : mellin shell (1/2:ℂ) = 0 := heM.trans hz
    apply hcontra hmnψ
    simpa only [show mellin (fun t : ℝ => ∑' j : ℕ, ψC (2^(j+1)*t)) (1/2:ℂ) = 0 from hzS] using hlim
end
