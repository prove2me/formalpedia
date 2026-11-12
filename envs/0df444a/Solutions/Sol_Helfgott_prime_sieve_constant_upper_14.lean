-- Prove2me | solution 1 for Helfgott.prime_sieve_constant_upper_14
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T15:29:49.010653+00:00
-- url     : https://prove2.me/submissions/8da296b8-210b-44a7-a2b2-9593ba3fea17

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

open Finset
open scoped BigOperators Classical
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

private noncomputable def f (n : ℕ) : ℝ := Real.log n / ((n : ℝ) * ((n : ℝ)-1))
private noncomputable def H (x : ℝ) : ℝ := Real.log x / x + 1/(x-1)

private lemma f_nonneg (n : ℕ) : 0 ≤ f n := by
  rcases n with _ | n
  · simp [f]
  · have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact div_nonneg (Real.log_nonneg hn) (mul_nonneg (by linarith) (by linarith))

private lemma log_two_bounds : (693147/1000000 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (693148/1000000 : ℝ) := by
  have hl := Real.sum_range_le_log_div (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (1/3:ℝ) < 1) 8
  have hu := Real.log_div_le_sum_range_add (by norm_num : (0:ℝ) ≤ 1/3)
    (by norm_num : (1/3:ℝ) < 1) 8
  norm_num [sum_range_succ] at hl hu
  constructor <;> linarith

private lemma gamma_upper : Real.eulerMascheroniConstant ≤ (3/5 : ℝ) := by
  have hg := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 32
  have hh : (harmonic 32 : ℝ) ≤ (203/50 : ℝ) := by norm_num [harmonic, sum_range_succ]
  have hlog : Real.log (32:ℝ) = 5 * Real.log 2 := by
    rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow]
    norm_num
  norm_num [Real.eulerMascheroniSeq'] at hg
  linarith [log_two_bounds.1]

private lemma scaled_log_upper (p b : ℝ) (k : ℕ) (U : ℝ)
    (hp : 0 < p) (hb : 0 < b) (hbp : b ≤ p) (hbpow : b = 2^k)
    (hnum : (k : ℝ) * (693148/1000000 : ℝ) +
      2 * ((∑ i ∈ range 6, ((p-b)/(p+b))^(2*i+1) / (2*i+1)) +
        ((p-b)/(p+b))^13 / (1-((p-b)/(p+b))^2)) ≤ U) :
    Real.log p ≤ U := by
  have hz0 : 0 ≤ (p-b)/(p+b) := div_nonneg (sub_nonneg.mpr hbp) (by linarith)
  have hz1 : (p-b)/(p+b) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hs := Real.log_div_le_sum_range_add hz0 hz1 6
  have heq : (1+(p-b)/(p+b))/(1-(p-b)/(p+b)) = p/b := by
    field_simp [ne_of_gt hb, ne_of_gt (add_pos hp hb)]
    ring
  have hlogb : Real.log b = (k : ℝ) * Real.log 2 := by rw [hbpow, Real.log_pow]
  rw [heq, Real.log_div (ne_of_gt hp) (ne_of_gt hb), hlogb] at hs
  norm_num only at hs
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [log_two_bounds.2]

private lemma prime_prefix_upper :
    (∑ n ∈ (range 128).filter Nat.Prime, f n) ≤ (3/4 : ℝ) := by
  have h2 : Real.log 2 ≤ (69317/100000 : ℝ) := by
    apply scaled_log_upper 2 2 1 (69317/100000) <;> norm_num [sum_range_succ]
  have h3 : Real.log 3 ≤ (109864/100000 : ℝ) := by
    apply scaled_log_upper 3 2 1 (109864/100000) <;> norm_num [sum_range_succ]
  have h5 : Real.log 5 ≤ (160946/100000 : ℝ) := by
    apply scaled_log_upper 5 4 2 (160946/100000) <;> norm_num [sum_range_succ]
  have h7 : Real.log 7 ≤ (194594/100000 : ℝ) := by
    apply scaled_log_upper 7 4 2 (194594/100000) <;> norm_num [sum_range_succ]
  have h11 : Real.log 11 ≤ (239792/100000 : ℝ) := by
    apply scaled_log_upper 11 8 3 (239792/100000) <;> norm_num [sum_range_succ]
  have h13 : Real.log 13 ≤ (256497/100000 : ℝ) := by
    apply scaled_log_upper 13 8 3 (256497/100000) <;> norm_num [sum_range_succ]
  have h17 : Real.log 17 ≤ (283324/100000 : ℝ) := by
    apply scaled_log_upper 17 16 4 (283324/100000) <;> norm_num [sum_range_succ]
  have h19 : Real.log 19 ≤ (294446/100000 : ℝ) := by
    apply scaled_log_upper 19 16 4 (294446/100000) <;> norm_num [sum_range_succ]
  have h23 : Real.log 23 ≤ (313552/100000 : ℝ) := by
    apply scaled_log_upper 23 16 4 (313552/100000) <;> norm_num [sum_range_succ]
  have h29 : Real.log 29 ≤ (336732/100000 : ℝ) := by
    apply scaled_log_upper 29 16 4 (336732/100000) <;> norm_num [sum_range_succ]
  have h31 : Real.log 31 ≤ (343401/100000 : ℝ) := by
    apply scaled_log_upper 31 16 4 (343401/100000) <;> norm_num [sum_range_succ]
  have h37 : Real.log 37 ≤ (361094/100000 : ℝ) := by
    apply scaled_log_upper 37 32 5 (361094/100000) <;> norm_num [sum_range_succ]
  have h41 : Real.log 41 ≤ (371360/100000 : ℝ) := by
    apply scaled_log_upper 41 32 5 (371360/100000) <;> norm_num [sum_range_succ]
  have h43 : Real.log 43 ≤ (376123/100000 : ℝ) := by
    apply scaled_log_upper 43 32 5 (376123/100000) <;> norm_num [sum_range_succ]
  have h47 : Real.log 47 ≤ (385017/100000 : ℝ) := by
    apply scaled_log_upper 47 32 5 (385017/100000) <;> norm_num [sum_range_succ]
  have h53 : Real.log 53 ≤ (397032/100000 : ℝ) := by
    apply scaled_log_upper 53 32 5 (397032/100000) <;> norm_num [sum_range_succ]
  have h59 : Real.log 59 ≤ (407756/100000 : ℝ) := by
    apply scaled_log_upper 59 32 5 (407756/100000) <;> norm_num [sum_range_succ]
  have h61 : Real.log 61 ≤ (411090/100000 : ℝ) := by
    apply scaled_log_upper 61 32 5 (411090/100000) <;> norm_num [sum_range_succ]
  have h67 : Real.log 67 ≤ (420472/100000 : ℝ) := by
    apply scaled_log_upper 67 64 6 (420472/100000) <;> norm_num [sum_range_succ]
  have h71 : Real.log 71 ≤ (426270/100000 : ℝ) := by
    apply scaled_log_upper 71 64 6 (426270/100000) <;> norm_num [sum_range_succ]
  have h73 : Real.log 73 ≤ (429048/100000 : ℝ) := by
    apply scaled_log_upper 73 64 6 (429048/100000) <;> norm_num [sum_range_succ]
  have h79 : Real.log 79 ≤ (436947/100000 : ℝ) := by
    apply scaled_log_upper 79 64 6 (436947/100000) <;> norm_num [sum_range_succ]
  have h83 : Real.log 83 ≤ (441887/100000 : ℝ) := by
    apply scaled_log_upper 83 64 6 (441887/100000) <;> norm_num [sum_range_succ]
  have h89 : Real.log 89 ≤ (448866/100000 : ℝ) := by
    apply scaled_log_upper 89 64 6 (448866/100000) <;> norm_num [sum_range_succ]
  have h97 : Real.log 97 ≤ (457474/100000 : ℝ) := by
    apply scaled_log_upper 97 64 6 (457474/100000) <;> norm_num [sum_range_succ]
  have h101 : Real.log 101 ≤ (461515/100000 : ℝ) := by
    apply scaled_log_upper 101 64 6 (461515/100000) <;> norm_num [sum_range_succ]
  have h103 : Real.log 103 ≤ (463475/100000 : ℝ) := by
    apply scaled_log_upper 103 64 6 (463475/100000) <;> norm_num [sum_range_succ]
  have h107 : Real.log 107 ≤ (467285/100000 : ℝ) := by
    apply scaled_log_upper 107 64 6 (467285/100000) <;> norm_num [sum_range_succ]
  have h109 : Real.log 109 ≤ (469137/100000 : ℝ) := by
    apply scaled_log_upper 109 64 6 (469137/100000) <;> norm_num [sum_range_succ]
  have h113 : Real.log 113 ≤ (472741/100000 : ℝ) := by
    apply scaled_log_upper 113 64 6 (472741/100000) <;> norm_num [sum_range_succ]
  have h127 : Real.log 127 ≤ (484421/100000 : ℝ) := by
    apply scaled_log_upper 127 64 6 (484421/100000) <;> norm_num [sum_range_succ]
  norm_num [sum_filter, sum_range_succ, f]
  linarith

private lemma tail_step (x : ℝ) (hx : 3 ≤ x) :
    Real.log x / (x*(x-1)) ≤ H (x-1) - H x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x-1 := by linarith
  have hx2 : 0 < x-2 := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hx0 hx1)
  rw [Real.log_div (ne_of_gt hx0) (ne_of_gt hx1)] at hl
  have heq : x/(x-1)-1 = 1/(x-1) := by field_simp; ring
  rw [heq] at hl
  have hrec : (1/(x-1))/(x-1) ≤ 1/(x-2)-1/(x-1) := by
    have hden : 1/(x-1) ≤ 1/(x-2) := one_div_le_one_div_of_le hx2 (by linarith)
    have h := div_le_div_of_nonneg_right hden hx1.le
    calc
      _ ≤ (1/(x-2))/(x-1) := h
      _ = _ := by field_simp; ring
  calc
    _ = Real.log (x-1)/(x-1) - Real.log x/x +
        (Real.log x-Real.log (x-1))/(x-1) := by field_simp; ring
    _ ≤ Real.log (x-1)/(x-1) - Real.log x/x + (1/(x-1))/(x-1) := by
      gcongr
    _ ≤ Real.log (x-1)/(x-1) - Real.log x/x + (1/(x-2)-1/(x-1)) := by linarith
    _ = H (x-1)-H x := by
      unfold H
      rw [show x-1-1 = x-2 by ring]
      ring

private lemma H_nonneg (x : ℝ) (hx : 2 ≤ x) : 0 ≤ H x := by
  unfold H
  exact add_nonneg (div_nonneg (Real.log_nonneg (by linarith)) (by linarith))
    (div_nonneg zero_le_one (by linarith))

private lemma tail_range (N : ℕ) : ∑ n ∈ range N, f (128+n) ≤ H 127 - H (127+N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hs := tail_step (128+N) (by have h := Nat.cast_nonneg (α := ℝ) N; linarith)
    have heq : (128:ℝ)+N-1 = 127+N := by ring
    rw [heq] at hs
    have hf : f (128+N) = Real.log (128+N : ℝ) / ((128+N)*(128+N-1)) := by
      simp [f]
    rw [hf, heq]
    push_cast
    rw [show (127:ℝ) + ((N:ℝ)+1) = 128+N by ring]
    linarith

private lemma H_127_upper : H 127 ≤ (1/20 : ℝ) := by
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 127) (by norm_num : (127:ℝ) ≤ 128)
  have heq : Real.log (128:ℝ) = 7 * Real.log 2 := by
    rw [show (128:ℝ) = 2^7 by norm_num, Real.log_pow]
    norm_num
  have h2 := log_two_bounds.2
  unfold H
  norm_num
  linarith

private lemma prime_sum_upper :
    (∑' p : {p : ℕ // p.Prime}, f p.val) ≤ (4/5 : ℝ) := by
  apply Real.tsum_le_of_sum_le (fun (p : {p : ℕ // p.Prime}) => f_nonneg p.val)
  intro P
  let A := (P.image Subtype.val).filter (fun n => n < 128)
  let B := (P.image Subtype.val).filter (fun n => ¬n < 128)
  have hsplit : ∑ p ∈ P, f p.val = (∑ n ∈ A, f n) + ∑ n ∈ B, f n := by
    rw [← sum_image (fun a _ b _ h => Subtype.ext h)]
    exact (sum_filter_add_sum_filter_not _ _ _).symm
  have hAsub : A ⊆ (range 128).filter Nat.Prime := by
    intro n hn
    obtain ⟨hnP, hn128⟩ := mem_filter.mp hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hnP
    exact mem_filter.mpr ⟨mem_range.mpr hn128, p.property⟩
  have hA : (∑ n ∈ A, f n) ≤ (3/4 : ℝ) :=
    (sum_le_sum_of_subset_of_nonneg hAsub (fun n _ _ => f_nonneg n)).trans prime_prefix_upper
  let N := P.sup Subtype.val + 1
  have hBsub : B ⊆ Ico 128 (128+N) := by
    intro n hn
    obtain ⟨hnP, hn128⟩ := mem_filter.mp hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hnP
    have hle : p.val ≤ P.sup Subtype.val := le_sup hp
    apply mem_Ico.mpr
    dsimp only [N]
    omega
  have hB : (∑ n ∈ B, f n) ≤ H 127 := by
    have h := sum_le_sum_of_subset_of_nonneg hBsub (fun n _ _ => f_nonneg n)
    rw [sum_Ico_eq_sum_range] at h
    simp only [Nat.add_sub_cancel_left] at h
    exact h.trans ((tail_range N).trans (sub_le_self _
      (H_nonneg _ (by have hn := Nat.cast_nonneg (α := ℝ) N; linarith))))
  rw [hsplit]
  linarith [H_127_upper]

theorem solution : Real.eulerMascheroniConstant +
    (∑' p : Nat.Primes, Real.log (p : ℕ) /
      (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)-1))) ≤ (7/5 : ℝ) := by
  have hp : (∑' p : Nat.Primes, Real.log (p : ℕ) /
      (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ)-1))) ≤ (4/5 : ℝ) := prime_sum_upper
  linarith [gamma_upper]
