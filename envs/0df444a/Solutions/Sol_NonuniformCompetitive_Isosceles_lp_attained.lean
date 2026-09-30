-- Prove2me | solution 1 for NonuniformCompetitive.Isosceles.lp_attained
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:08:26.196438+00:00
-- url     : https://prove2.me/submissions/c769dd7c-dfd8-4e74-a63c-f7dd5b80f353

import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio
import Mathlib.Tactic
open NonuniformCompetitive.Isosceles
open scoped BigOperators

private theorem tight_sum (P a : ℝ) (hP : 1 < P) (k : ℕ) :
    ∑ i∈Finset.Icc 1 k, (1-(a-1)*((P/(P-1))^i-1)) =
      a*k-P*(a-1)*((P/(P-1))^k-1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1),ih,pow_succ]
    push_cast
    field_simp [ne_of_gt (sub_pos.mpr hP)]
    ring

private theorem prefix_bound (P a : ℝ) (hP : 1 < P) (π : ℕ → ℝ) (N : ℕ)
    (hcon : ∀ k, 1 ≤ k → k ≤ N → π k*P+∑ i∈Finset.Icc 1 k, (1-π i)≤a*k) :
    ∑ i∈Finset.Icc 1 N, π i ≤ (a-1)*(P*((P/(P-1))^N-1)-N) := by
  let S (k : ℕ) : ℝ := ∑ i∈Finset.Icc 1 k, π i
  have hb : ∀ k ≤ N, S k≤(a-1)*(P*((P/(P-1))^k-1)-k) := by
    intro k
    induction k with
    | zero => intro hk; simp [S]
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hc := hcon (k+1) (by omega) hk
      simp [Finset.sum_sub_distrib] at hc
      have hS : S (k+1)=S k+π (k+1) := Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1) π
      change π (k+1)*P + ((k:ℝ)+1-S (k+1)) ≤ a*((k:ℝ)+1) at hc
      rw [hS] at hc
      push_cast at hc
      have hid : (P-1)*((a-1)*((P/(P-1))^(k+1)-1)) =
          (a-1)*(1+P*((P/(P-1))^k-1)) := by
        rw [pow_succ]
        field_simp [ne_of_gt (sub_pos.mpr hP)]
        ring
      have hpi : π (k+1)≤(a-1)*((P/(P-1))^(k+1)-1) := by
        apply (mul_le_mul_iff_right₀ (sub_pos.mpr hP)).mp
        nlinarith [hid]
      have hid2 : (a-1)*(P*((P/(P-1))^(k+1)-1)-(k+1)) =
          (a-1)*(P*((P/(P-1))^k-1)-k)+(a-1)*((P/(P-1))^(k+1)-1) := by
        rw [pow_succ]
        field_simp [ne_of_gt (sub_pos.mpr hP)]
        ring
      rw [hS]
      push_cast
      rw [hid2]
      exact add_le_add ih' hpi
  exact hb N le_rfl

private theorem ratio_parameters (d : ℕ) (hd : 1 ≤ d) :
    1 < eTwoDSubOne d ∧ 0 < isoscelesRatio d-1 ∧
      (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d))=1-1/(4*d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1 : ℝ) < 2*d := by linarith
  have hr : (1 : ℝ) < (2*d)/(2*d-1) := by apply (lt_div_iff₀ (by linarith)).mpr; linarith
  have he : 1 < eTwoDSubOne d := by unfold eTwoDSubOne; exact one_lt_pow₀ hr (by omega)
  have hden : 0 < eTwoDSubOne d-1+1/(2*d) := by positivity
  have hsmall : 1/(4*(d:ℝ)) < 1 := by apply (div_lt_one (by positivity)).mpr; linarith
  have hid : (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d))=1-1/(4*d) := by
    unfold isoscelesRatio
    rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hden)]
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
    ring
  refine ⟨he,?_,hid⟩
  have hh : 0 < (isoscelesRatio d-1)*(eTwoDSubOne d-1+1/(2*d)) := by rw [hid]; linarith
  exact (mul_pos_iff_of_pos_right hden).mp hh

theorem solution (d : ℕ) (hd : 1 ≤ d) (π : ℕ → ℝ)
    (hπ : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d - 1 →
      π k = (isoscelesRatio d - 1) * (((2 * d : ℝ) / (2 * d - 1)) ^ k - 1))
    (hπ2d : π (2 * d) = 1) :
    0 ≤ π 1 ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d → π k ≤ π (k + 1)) ∧
    (∀ k : ℕ, 1 ≤ k → k < 2 * d →
      π k * (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 k, (1 - π i) = isoscelesRatio d * (k : ℝ)) ∧
    (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 (2 * d - 1), (1 - π i) + 1 / 2
      = isoscelesRatio d * (2 * d : ℝ) := by
  obtain ⟨he,ha,hid⟩ := ratio_parameters d hd
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1:ℝ) < 2*d := by linarith
  have hr : (1:ℝ) < (2*d)/(2*d-1) := by apply (lt_div_iff₀ (by linarith)).mpr; linarith
  have hN : ((2*d-1:ℕ):ℝ)=2*(d:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hs (k : ℕ) (hk : k ≤ 2*d-1) :
      ∑ i∈Finset.Icc 1 k, (1-π i) =
        isoscelesRatio d*k-(2*d)*(isoscelesRatio d-1)*(((2*d:ℝ)/(2*d-1))^k-1) := by
    calc
      _ = ∑ i∈Finset.Icc 1 k, (1-(isoscelesRatio d-1)*(((2*d:ℝ)/(2*d-1))^i-1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hπ i (Finset.mem_Icc.mp hi).1 (le_trans (Finset.mem_Icc.mp hi).2 hk)]
      _ = _ := tight_sum _ _ hP k
  have hlast : (isoscelesRatio d-1)*((2*d)*(eTwoDSubOne d-1)+1)=2*d-1/2 := by
    have hh := congrArg (fun z : ℝ => z*(2*d)) hid
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)] at hh
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · rw [hπ 1 (by omega) (by omega)]
    exact mul_nonneg ha.le (sub_nonneg.mpr (one_le_pow₀ hr.le))
  · intro k hk1 hk
    by_cases hkend : k+1=2*d
    · rw [hkend,hπ2d,hπ k hk1 (by omega)]
      have hkN : k=2*d-1 := by omega
      rw [hkN]
      change (isoscelesRatio d-1)*(eTwoDSubOne d-1) ≤ 1
      have hterm : 0 ≤ (isoscelesRatio d-1)/(2*d) := by positivity
      have hsmall : 0 ≤ 1/(4*(d:ℝ)) := by positivity
      nlinarith [hid]
    · rw [hπ k hk1 (by omega),hπ (k+1) (by omega) (by omega)]
      apply mul_le_mul_of_nonneg_left _ ha.le
      apply sub_le_sub_right
      exact pow_le_pow_right₀ hr.le (by omega)
  · intro k hk1 hk
    rw [hs k (by omega),hπ k hk1 (by omega)]
    ring
  · rw [hs _ le_rfl,hN]
    change 2*(d:ℝ)+ (isoscelesRatio d*(2*d-1)-(2*d)*(isoscelesRatio d-1)*(eTwoDSubOne d-1))+1/2 = isoscelesRatio d*(2*d)
    nlinarith [hlast]
