-- Prove2me | solution 1 for NonuniformCompetitive.Isosceles.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:14:26.559984+00:00
-- url     : https://prove2.me/submissions/d0c9092f-1e4b-46f0-9c0f-46e5aee0e083

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

theorem solution (d : ℕ) (hd : 1 ≤ d) (π : ℕ → ℝ) (α : ℝ)
    (hlt : ∀ k : ℕ, 1 ≤ k → k < 2 * d →
      π k * (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 k, (1 - π i) ≤ α * (k : ℝ))
    (hge : (2 * d : ℝ) + ∑ i ∈ Finset.Icc 1 (2 * d - 1), (1 - π i) + 1 / 2 ≤ α * (2 * d : ℝ)) :
    isoscelesRatio d ≤ α := by
  obtain ⟨he,ha,hid⟩ := ratio_parameters d hd
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hP : (1:ℝ) < 2*d := by linarith
  have hN : ((2*d-1:ℕ):ℝ)=2*(d:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hb := prefix_bound (2*d) α hP π (2*d-1) (fun k hk1 hk => hlt k hk1 (by omega))
  rw [hN] at hb
  change (∑ i∈Finset.Icc 1 (2*d-1), π i) ≤ (α-1)*((2*d)*(eTwoDSubOne d-1)-(2*d-1)) at hb
  have hg := hge
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,Nat.sub_zero,nsmul_eq_mul,mul_one] at hg
  rw [hN] at hg
  have hden : 0 < eTwoDSubOne d-1+1/(2*d) := by positivity
  unfold isoscelesRatio
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_right₀ (by linarith : (0:ℝ) < 2*d)).mp
  have hl : (eTwoDSubOne d+1/(4*d))*(2*d)=(2*d)*eTwoDSubOne d+1/2 := by
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
    ring
  have hr : (α*(eTwoDSubOne d-1+1/(2*d)))*(2*d)=α*((2*d)*(eTwoDSubOne d-1)+1) := by
    field_simp [ne_of_gt (by linarith : (0:ℝ) < d)]
  nlinarith [hl,hr]
