-- Prove2me | solution 1 for NymanBeurling.nonnegative_coefficients_cost_ge_one_div_42
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:53:21.761569+00:00
-- url     : https://prove2.me/submissions/3ca8ae89-3a8d-41ad-aa80-45efdd1a7637

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

namespace PositiveCertificate

private def y (i : ℕ) : ℚ := ([8981,847,-2073,312,-2996,2364,-792,-184,-480,726,-888,743,
  -592,-153,307,386,-390,204,-427,11,137,168,-266,144,-15,-20,-58,93,-180,
  181,-64,-31,-25,-28,-32,145,-28,-35,-47,57,-81,77] : List ℚ).getD i 0

private def w (i : ℕ) : ℚ := ((i:ℚ)+1)*((i:ℚ)+2)
private def e (c : ℕ →₀ ℚ) (i : ℕ) : ℚ :=
  1 - ∑ k ∈ c.support, c k * (((i+1)%(k+2):ℕ):ℚ) / ((k+2:ℕ):ℚ)
private def T (c : ℕ →₀ ℚ) (i : ℕ) : ℚ := (e c i)^2 / w i
private def a : ℚ := 5998/1504383920

private lemma sum_y : ∑ i ∈ Finset.range 42, y i = 5998 := by decide +kernel
private lemma sum_y_sq : ∑ i ∈ Finset.range 42, w i * (y i)^2 = 1504383920 := by decide +kernel

private lemma col (d : ℕ) : ∑ i ∈ Finset.range 42, y i * (((i+1)%d:ℕ):ℚ) ≤ 0 := by
  have small : ∀ d : Fin 43, ∑ i ∈ Finset.range 42, y i * (((i+1)%(d:ℕ):ℕ):ℚ) ≤ 0 := by decide +kernel
  by_cases hd : d<43
  · exact small ⟨d,hd⟩
  · have he (i : ℕ) (hi : i ∈ Finset.range 42) : (i+1)%d = i+1 := by
      apply Nat.mod_eq_of_lt
      have := Finset.mem_range.mp hi
      omega
    calc
      _ = ∑ i ∈ Finset.range 42, y i * ((i+1:ℕ):ℚ) :=
        Finset.sum_congr rfl (fun i hi => by rw [he i hi])
      _ ≤ 0 := by simpa only [Fin.val_zero, Nat.mod_zero] using small (0 : Fin 43)

private lemma pairing (c : ℕ →₀ ℚ) (hc : ∀ k, 0 ≤ c k) :
    5998 ≤ ∑ i ∈ Finset.range 42, y i * e c i := by
  have swap : (∑ i ∈ Finset.range 42, y i * ∑ k ∈ c.support,
        c k * (((i+1)%(k+2):ℕ):ℚ) / ((k+2:ℕ):ℚ)) =
      ∑ k ∈ c.support, (c k / ((k+2:ℕ):ℚ)) *
        ∑ i ∈ Finset.range 42, y i * (((i+1)%(k+2):ℕ):ℚ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hn : (∑ k ∈ c.support, (c k / ((k+2:ℕ):ℚ)) *
        ∑ i ∈ Finset.range 42, y i * (((i+1)%(k+2):ℕ):ℚ)) ≤ 0 :=
    Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (div_nonneg (hc k) (by positivity)) (col _)
  simp_rw [e, mul_sub, mul_one, Finset.sum_sub_distrib, sum_y, swap]
  linarith

private lemma prefix_bound (c : ℕ →₀ ℚ) (hc : ∀ k, 0 ≤ c k) :
    1/42 ≤ ∑ i ∈ Finset.range 42, T c i := by
  have pt (i : ℕ) : 2*a*(y i*e c i) - a^2*(w i*y i^2) ≤ T c i := by
    have hw : 0 < w i := by unfold w; positivity
    apply (le_div_iff₀ hw).mpr
    nlinarith [sq_nonneg (e c i - a*w i*y i)]
  have hs := Finset.sum_le_sum (s:=Finset.range 42) (fun i _ => pt i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_y_sq] at hs
  have h := pairing c hc
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2*a by norm_num [a])
  norm_num [a] at hs h'
  linarith

end PositiveCertificate

open PositiveCertificate

theorem solution (c : ℕ →₀ ℚ) (hc : ∀ k, 0 ≤ c k) (H : ℕ) :
    (1/42 : ℚ) ≤ (∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) := by
  change _ ≤ (∑ n ∈ Finset.range H, T c n) + _
  have ht (n : ℕ) : 0 ≤ T c n := by unfold T w; positivity
  by_cases h : 42 ≤ H
  · have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun i _ _ => ht i)
    exact (prefix_bound c hc).trans (hsum.trans (le_add_of_nonneg_right (by positivity)))
  · have hH : (H:ℚ)+1 ≤ 42 := by exact_mod_cast (by omega : H+1 ≤ 42)
    have hM := Finset.sum_nonneg (s:=c.support) (fun k _ => abs_nonneg (c k))
    have htail : (1:ℚ)/42 ≤ (1 + ∑ k ∈ c.support, |c k|)^2/((H:ℚ)+1) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (∑ k ∈ c.support, |c k|)]
    exact htail.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun n _ => ht n))
