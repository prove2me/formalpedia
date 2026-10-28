-- Prove2me | solution 1 for LL_Linnik1536a.moment_SL_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:55:14.374017+00:00
-- url     : https://prove2.me/submissions/635ddfc4-a406-471a-9484-aec9c7ec281a

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace A3S89LLs

noncomputable def E (n : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * ((n : ℂ) * x))

lemma E_cont (n : ℤ) : Continuous (E n) := by
  unfold E; fun_prop

lemma E_zero (x : ℝ) : E 0 x = 1 := by simp [E]

lemma E_add (n m : ℤ) (x : ℝ) : E n x * E m x = E (n + m) x := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma E_conj (n : ℤ) (x : ℝ) : (starRingEnd ℂ) (E n x) = E (-n) x := by
  unfold E; rw [← Complex.exp_conj]; congr 1
  simp [map_mul, Complex.conj_ofReal, map_ofNat]

lemma E_int (n : ℤ) : ∫ x in (0 : ℝ)..1, E n x = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [E_zero]
  · have hc : (2 * π * Complex.I * n) ≠ 0 := by
      have := Real.pi_pos
      simp [h, Real.pi_ne_zero, Complex.I_ne_zero]
    have : (fun x : ℝ => E n x) = fun x : ℝ => Complex.exp ((2 * π * Complex.I * n) * x) := by
      funext x; unfold E; congr 1; ring
    rw [this, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

def Good (f : ℝ → ℂ) : Prop :=
  ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum

lemma good_one : Good (fun _ => 1) := ⟨{0}, fun x => by simp [E_zero]⟩

lemma msum_mul (s t : Multiset ℤ) (x : ℝ) :
    (s.map fun n => E n x).sum * (t.map fun n => E n x).sum =
      ((s.bind fun a => t.map fun b => a + b).map fun n => E n x).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, add_mul, ih, Multiset.cons_bind,
      Multiset.map_add, Multiset.sum_add, Multiset.map_map]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp [E_add]

lemma good_mul {f g : ℝ → ℂ} (hf : Good f) (hg : Good g) : Good (fun x => f x * g x) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨_, fun x => by show f x * g x = _; rw [hs, ht, msum_mul]⟩

lemma good_pow {f : ℝ → ℂ} (hf : Good f) (p : ℕ) : Good (fun x => f x ^ p) := by
  induction p with
  | zero => simpa using good_one
  | succ p ih =>
    simpa [pow_succ] using good_mul ih hf

lemma msum_int (s : Multiset ℤ) :
    ∫ x in (0 : ℝ)..1, (s.map fun n => E n x).sum = ((s.count 0 : ℕ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hc : Continuous fun x => (s.map fun n => E n x).sum := by
      apply continuous_multiset_sum; intro i _; exact E_cont i
    rw [intervalIntegral.integral_add ((E_cont a).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), ih, E_int, Multiset.count_cons]
    by_cases h : a = 0
    · subst h; simp; ring
    · simp [h, Ne.symm h]

lemma good_int {f : ℝ → ℂ} (hf : Good f) : ∃ N : ℕ, ∫ x in (0 : ℝ)..1, f x = N := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨_, by simp_rw [hs]; exact msum_int s⟩

lemma G_eq (L : ℕ) (x : ℝ) :
    LL_Linnik1536a.Gpow L x = ∑ k ∈ range L, E (2 ^ k) x := by
  unfold LL_Linnik1536a.Gpow E; push_cast; rfl

lemma good_G (L : ℕ) : Good (LL_Linnik1536a.Gpow L) := by
  refine ⟨(range L).val.map fun k => (2 : ℤ) ^ k, fun x => ?_⟩
  rw [G_eq, Multiset.map_map, Finset.sum_eq_multiset_sum]; rfl

lemma good_Gc (L : ℕ) : Good (fun x => (starRingEnd ℂ) (LL_Linnik1536a.Gpow L x)) := by
  refine ⟨(range L).val.map fun k => -(2 : ℤ) ^ k, fun x => ?_⟩
  show (starRingEnd ℂ) (LL_Linnik1536a.Gpow L x) = _
  rw [G_eq, map_sum, Multiset.map_map, Finset.sum_eq_multiset_sum]
  simp only [E_conj]; rfl

lemma G_cont (L : ℕ) : Continuous (LL_Linnik1536a.Gpow L) := by
  unfold LL_Linnik1536a.Gpow; fun_prop

lemma S_re (L : ℕ) (x : ℝ) : LL_Linnik1536a.Spow L x = (LL_Linnik1536a.Gpow L x).re := by
  unfold LL_Linnik1536a.Spow LL_Linnik1536a.Gpow
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2 * π * Complex.I * ((2 : ℂ) ^ k * x)) = ((2 * π * ((2 : ℝ) ^ k * x) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

lemma twoS (L : ℕ) (x : ℝ) : ((2 * LL_Linnik1536a.Spow L x : ℝ) : ℂ) =
    LL_Linnik1536a.Gpow L x + (starRingEnd ℂ) (LL_Linnik1536a.Gpow L x) := by
  rw [Complex.add_conj, S_re]

lemma normpow (z : ℂ) (j : ℕ) : ((‖z‖ ^ (2 * j) : ℝ) : ℂ) = z ^ j * (starRingEnd ℂ z) ^ j := by
  rw [← mul_pow, Complex.mul_conj, pow_mul, Complex.sq_norm]; push_cast; rfl

lemma Ipq (L p q : ℕ) : ∃ N : ℕ, ∫ x in (0 : ℝ)..1,
    LL_Linnik1536a.Gpow L x ^ p * (starRingEnd ℂ) (LL_Linnik1536a.Gpow L x) ^ q = N :=
  good_int (good_mul (good_pow (good_G L) p) (good_pow (good_Gc L) q))

end A3S89LLs

open A3S89LLs in
theorem solution (L n : ℕ) : 0 ≤ ∫ x in (0 : ℝ)..1, LL_Linnik1536a.Spow L x ^ n := by
  choose N hN using Ipq L
  set G := LL_Linnik1536a.Gpow L
  have hGc : Continuous G := G_cont L
  have hGcc : Continuous fun x => (starRingEnd ℂ) (G x) := by fun_prop
  have h2 : ∫ x in (0 : ℝ)..1, (2 * LL_Linnik1536a.Spow L x) ^ n =
      ∑ k ∈ range (n + 1), (N k (n - k) : ℝ) * (n.choose k : ℝ) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [Complex.ofReal_pow, twoS, add_pow]
    rw [intervalIntegral.integral_finsetSum]
    · push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_mul_const, hN]
    · intro k _
      apply Continuous.intervalIntegrable
      exact ((hGc.pow _).mul (hGcc.pow _)).mul continuous_const
  have h3 : ∫ x in (0 : ℝ)..1, (2 * LL_Linnik1536a.Spow L x) ^ n =
      2 ^ n * ∫ x in (0 : ℝ)..1, LL_Linnik1536a.Spow L x ^ n := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x
    rw [mul_pow]
  have h4 : (0 : ℝ) ≤ ∑ k ∈ range (n + 1), (N k (n - k) : ℝ) * (n.choose k : ℝ) := by
    positivity
  rw [← h2, h3] at h4
  exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ n) |> fun h => h
