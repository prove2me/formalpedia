-- Prove2me | solution 2 for NymanBeurling.subpower_remainder_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T04:06:39.352951+00:00
-- url     : https://prove2.me/submissions/a746941e-c42d-42b6-8ea8-fe9eb3d9663b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

private lemma certificate_controls_prefix (c : ℕ →₀ ℚ) (K H : ℕ) :
    (∑ n ∈ Finset.range H,
      (1 - ∑ k ∈ c.support, c k * (((n+1)%(k+2) : ℕ) : ℚ) / (k+2 : ℚ))^2 /
        ((n+1 : ℚ)*(n+2 : ℚ))) ≤
    (∑ n ∈ Finset.range K,
      (1 - ∑ k ∈ c.support, c k * (((n+1)%(k+2) : ℕ) : ℚ) / (k+2 : ℚ))^2 /
        ((n+1 : ℚ)*(n+2 : ℚ))) + (1+∑ k∈c.support, |c k|)^2/(K+1 : ℚ) := by
  let B : ℚ := 1+∑ k∈c.support, |c k|
  let R : ℕ → ℚ := fun n => 1 - ∑ k∈c.support,
    c k * (((n+1)%(k+2) : ℕ) : ℚ) / (k+2 : ℚ)
  let E : ℕ → ℚ := fun n => (R n)^2/((n+1 : ℚ)*(n+2 : ℚ))
  let C : ℕ → ℚ := fun K => (∑ n∈Finset.range K,E n)+B^2/(K+1 : ℚ)
  have hR (n : ℕ) : |R n| ≤ B := by
    calc
      |R n| ≤ |(1 : ℚ)| + |∑ k∈c.support,
        c k * (((n+1)%(k+2) : ℕ) : ℚ) / (k+2 : ℚ)| := abs_sub _ _
      _ ≤ 1 + ∑ k∈c.support,
          |c k * (((n+1)%(k+2) : ℕ) : ℚ) / (k+2 : ℚ)| := by
        simpa using add_le_add_left (Finset.abs_sum_le_sum_abs _ _) (1 : ℚ)
      _ ≤ B := by
        dsimp [B]
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℚ) ≤ ((n+1)%(k+2):ℕ)),
          abs_of_pos (by positivity : (0:ℚ) < k+2)]
        apply (div_le_iff₀ (by positivity : (0:ℚ) < k+2)).2
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt (n+1) (by omega : 0<k+2)).le) (abs_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE (n : ℕ) : 0 ≤ E n := by dsimp [E]; positivity
  have hsq (n : ℕ) : (R n)^2 ≤ B^2 := by
    nlinarith [sq_abs (R n), hR n, abs_nonneg (R n)]
  have hC : Antitone C := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [C]
    rw [Finset.sum_range_succ]
    have hn : (0 : ℚ) < n+1 := by positivity
    have hn2 : (0 : ℚ) < n+2 := by positivity
    have hbound : E n ≤ B^2/((n+1 : ℚ)*(n+2 : ℚ)) :=
      div_le_div_of_nonneg_right (hsq n) (by positivity)
    have heq : B^2/((n+1 : ℚ)*(n+2 : ℚ)) + B^2/((n+1 : ℕ)+1 : ℚ) = B^2/(n+1 : ℚ) := by
      push_cast
      field_simp
      <;> ring
    linarith
  change (∑ n∈Finset.range H,E n) ≤ C K
  by_cases hKH : K ≤ H
  · exact (le_add_of_nonneg_right (by positivity : 0≤ B^2/(H+1 : ℚ))).trans (hC hKH)
  · have hprefix : (∑ n∈Finset.range H,E n) ≤ ∑ n∈Finset.range K,E n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ => hE n)
    exact hprefix.trans (le_add_of_nonneg_right (by positivity))

theorem solution (J L : ℕ) :
  ∃ (H K : ℕ) (c : ℕ→₀ℚ), L≤H ∧ (
    let R := fun n : ℕ => 1-∑ k∈c.support,c k*((((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))
    let E := fun n : ℕ => ((R n)^2/((n+1:ℚ)*(n+2:ℚ)):ℚ)
    let C : ℚ := (∑ n∈Finset.range K,E n)+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ)
    (∑ n∈Finset.range H,E n)≤1/(J+1:ℚ) ∧ C^(J+1)≤(H+1:ℚ)) := by
  obtain ⟨c,K,hc⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  refine ⟨L,K,c,le_rfl,?_⟩
  dsimp only
  simp only [Nat.cast_add, Nat.cast_ofNat, ← mul_div_assoc] at hc ⊢
  have hprefix := certificate_controls_prefix c K L
  constructor
  · exact hprefix.trans hc.le
  · have hnonneg : (0 : ℚ) ≤
        (∑ n∈Finset.range K,(1-∑ k∈c.support,c k*(((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))^2 /
          ((n+1:ℚ)*(n+2:ℚ)))+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ) := by positivity
    have hcost :
        (∑ n∈Finset.range K,(1-∑ k∈c.support,c k*(((n+1)%(k+2):ℕ):ℚ)/(k+2:ℚ))^2 /
          ((n+1:ℚ)*(n+2:ℚ)))+(1+∑ k∈c.support,|c k|)^2/(K+1:ℚ) ≤ 1 := by
      have hden : (1 : ℚ)/(J+1 : ℚ) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : (0:ℚ)<J+1)).2
        norm_num
      exact hc.le.trans hden
    exact (pow_le_one₀ (n := J+1) hnonneg hcost).trans (by have hL : (0:ℚ) ≤ L := Nat.cast_nonneg L; linarith)
