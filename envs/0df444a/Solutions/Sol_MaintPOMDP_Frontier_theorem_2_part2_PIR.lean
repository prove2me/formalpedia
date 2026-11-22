-- Prove2me | solution 1 for MaintPOMDP.Frontier.theorem_2_part2_PIR
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:20:38.87131+00:00
-- url     : https://prove2.me/submissions/5900d277-924b-424a-9aea-838652475bb4

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
import Theorems.Thm_MaintPOMDP_Frontier_solves_of_bellman_fixed_point
import Theorems.Thm_MaintPOMDP_Frontier_lemma_3
import Theorems.Thm_MaintPOMDP_Frontier_lemma_7

open Filter Topology

namespace MaintPOMDP.Frontier

section Helpers

private lemma prodSeq_step (M : Params) (u0 : Vec) (uF : ℝ) (i : ℕ) :
    (M.prodSeq u0 uF (i + 1)) 0 = M.β * dot M.p0 (M.prodSeq u0 uF i) ∧
    (M.prodSeq u0 uF (i + 1)) 1 =
      (M.cP + M.β * M.γ1 * uF) + M.ρ1 * (M.prodSeq u0 uF i) 1 := by
  constructor
  · simp [Params.prodSeq, Params.gP, Params.PP]
  · simp [Params.prodSeq, Params.gP, Params.PP, dot, Params.p1, Params.ρ1]
    ring

private lemma standing_aux (M : Params) (hM : M.Standing) :
    0 < M.γ0bar ∧ M.γ0bar < 1 ∧ 0 < M.γ1bar ∧ M.γ1bar < 1 ∧
    0 < M.ρ0 ∧ M.ρ0 < 1 ∧ 0 < M.ρ1 ∧ M.ρ1 < 1 ∧
    0 < M.ρ0bar ∧ 0 < M.ρ1bar ∧ 0 < M.D ∧ 0 < M.thrP := by
  have ⟨hb0, hb1, hcP, hPI, hIR, hRF, hg00, hg01, hg10, hg11⟩ := hM
  have hcF : 0 < M.cF := by linarith only [hcP, hPI, hIR, hRF]
  have h0b0 : 0 < M.γ0bar := by unfold Params.γ0bar; linarith only [hg01]
  have h0b1 : M.γ0bar < 1 := by unfold Params.γ0bar; linarith only [hg00]
  have h1b0 : 0 < M.γ1bar := by unfold Params.γ1bar; linarith only [hg11]
  have h1b1 : M.γ1bar < 1 := by unfold Params.γ1bar; linarith only [hg10]
  have hr00 : 0 < M.ρ0 := mul_pos hb0 h0b0
  have hr01 : M.ρ0 < 1 := by unfold Params.ρ0; nlinarith only [hb0, hb1, h0b0, h0b1]
  have hr10 : 0 < M.ρ1 := mul_pos hb0 h1b0
  have hr11 : M.ρ1 < 1 := by unfold Params.ρ1; nlinarith only [hb0, hb1, h1b0, h1b1]
  have hr0b : 0 < M.ρ0bar := by unfold Params.ρ0bar; linarith only [hr01]
  have hr1b : 0 < M.ρ1bar := by unfold Params.ρ1bar; linarith only [hr11]
  have hD : 0 < M.D := by
    unfold Params.D
    have : 0 < M.β * (M.γ0 + M.γ1) := mul_pos hb0 (add_pos hg00 hg10)
    linarith only [hb1, this]
  have hthr : 0 < M.thrP := by
    unfold Params.thrP
    exact div_pos (add_pos hcP (mul_pos (mul_pos hb0 hg10) hcF)) hD
  exact ⟨h0b0, h0b1, h1b0, h1b1, hr00, hr01, hr10, hr11, hr0b, hr1b, hD, hthr⟩

private lemma prodSeq_closed (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1)
    (u0 : Vec) (uF : ℝ) (i : ℕ) :
    let K := M.cP + M.β * M.γ1 * uF
    (M.prodSeq u0 uF i) 1 = (u0 1 - K / M.ρ1bar) * M.ρ1 ^ i + K / M.ρ1bar ∧
    (M.prodSeq u0 uF i) 0 =
      (u0 0 - M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar) +
        M.γ0 / (M.γ1 - M.γ0) * (u0 1 - K / M.ρ1bar)) * M.ρ0 ^ i
      - M.γ0 / (M.γ1 - M.γ0) * (u0 1 - K / M.ρ1bar) * M.ρ1 ^ i
      + M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar) := by
  have ⟨_, _, _, _, _, _, _, _, hr0b, hr1b, _, _⟩ := standing_aux M hM
  have h0 : M.ρ0bar ≠ 0 := hr0b.ne'
  have h1 : M.ρ1bar ≠ 0 := hr1b.ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  induction i with
  | zero =>
    simp only [Params.prodSeq, pow_zero, mul_one]
    constructor
    · ring
    · field_simp
      ring
  | succ i ih =>
    obtain ⟨ih1, ih0⟩ := ih
    obtain ⟨s0, s1⟩ := prodSeq_step M u0 uF i
    simp only [dot, Params.p0, Matrix.cons_val_zero, Matrix.cons_val_one] at s0
    rw [s0, s1, ih0, ih1]
    simp only [pow_succ]
    simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar] at h0 h1 ⊢
    constructor
    · field_simp
      ring
    · field_simp
      ring

private lemma prodSeq_tendsto (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1)
    (u0 : Vec) (uF : ℝ) :
    let K := M.cP + M.β * M.γ1 * uF
    Tendsto (fun i => (M.prodSeq u0 uF i) 0) atTop
      (𝓝 (M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar))) ∧
    Tendsto (fun i => (M.prodSeq u0 uF i) 1) atTop (𝓝 (K / M.ρ1bar)) := by
  have ⟨_, _, _, _, hr00, hr01, hr10, hr11, _, _, _, _⟩ := standing_aux M hM
  have ht0 : Tendsto (fun i : ℕ => M.ρ0 ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr00.le hr01
  have ht1 : Tendsto (fun i : ℕ => M.ρ1 ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr10.le hr11
  set K := M.cP + M.β * M.γ1 * uF
  set A0 := u0 0 - M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar) +
      M.γ0 / (M.γ1 - M.γ0) * (u0 1 - K / M.ρ1bar)
  set B0 := M.γ0 / (M.γ1 - M.γ0) * (u0 1 - K / M.ρ1bar)
  set C0 := M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar)
  set A1 := u0 1 - K / M.ρ1bar
  constructor
  · have heq : (fun i => (M.prodSeq u0 uF i) 0) = fun i => A0 * M.ρ0 ^ i - B0 * M.ρ1 ^ i + C0 := by
      funext i; exact (prodSeq_closed M hM hγ u0 uF i).2
    rw [heq]
    have hlim := ((ht0.const_mul A0).sub (ht1.const_mul B0)).add_const C0
    simpa using hlim
  · have heq : (fun i => (M.prodSeq u0 uF i) 1) = fun i => A1 * M.ρ1 ^ i + K / M.ρ1bar := by
      funext i; exact (prodSeq_closed M hM hγ u0 uF i).1
    rw [heq]
    have hlim := (ht1.const_mul A1).add_const (K / M.ρ1bar)
    simpa using hlim

private lemma prodSeq_diff_bounds (M : Params) (hM : M.Standing)
    (u0 v0 : Vec) (uF : ℝ)
    (h0l : 0 ≤ v0 0 - u0 0) (h0u : v0 0 - u0 0 ≤ 1)
    (h1l : 0 ≤ v0 1 - u0 1) (h1u : v0 1 - u0 1 ≤ 1) (i : ℕ) :
    (0 ≤ (M.prodSeq v0 (uF + 1) i) 0 - (M.prodSeq u0 uF i) 0 ∧
     (M.prodSeq v0 (uF + 1) i) 0 - (M.prodSeq u0 uF i) 0 ≤ 1) ∧
    (0 ≤ (M.prodSeq v0 (uF + 1) i) 1 - (M.prodSeq u0 uF i) 1 ∧
     (M.prodSeq v0 (uF + 1) i) 1 - (M.prodSeq u0 uF i) 1 ≤ 1) := by
  have ⟨hb0, hb1, _, _, _, _, hg00, hg01, hg10, hg11⟩ := hM
  induction i with
  | zero => exact ⟨⟨h0l, h0u⟩, ⟨h1l, h1u⟩⟩
  | succ i ih =>
    obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := ih
    obtain ⟨sv0, sv1⟩ := prodSeq_step M v0 (uF + 1) i
    obtain ⟨su0, su1⟩ := prodSeq_step M u0 uF i
    rw [sv0, su0, sv1, su1]
    simp only [dot, Params.p0, Params.γ0bar, Params.ρ1, Params.γ1bar,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    set d0 := (M.prodSeq v0 (uF + 1) i) 0 - (M.prodSeq u0 uF i) 0 with hd0
    set d1 := (M.prodSeq v0 (uF + 1) i) 1 - (M.prodSeq u0 uF i) 1 with hd1
    have e0 : M.β * ((1 - M.γ0) * (M.prodSeq v0 (uF + 1) i) 0 +
          M.γ0 * (M.prodSeq v0 (uF + 1) i) 1) -
        M.β * ((1 - M.γ0) * (M.prodSeq u0 uF i) 0 +
          M.γ0 * (M.prodSeq u0 uF i) 1) =
        M.β * ((1 - M.γ0) * d0 + M.γ0 * d1) := by rw [hd0, hd1]; ring
    have e1 : M.cP + M.β * M.γ1 * (uF + 1) +
          M.β * (1 - M.γ1) * (M.prodSeq v0 (uF + 1) i) 1 -
        (M.cP + M.β * M.γ1 * uF +
          M.β * (1 - M.γ1) * (M.prodSeq u0 uF i) 1) =
        M.β * (M.γ1 + (1 - M.γ1) * d1) := by rw [hd1]; ring
    rw [e0, e1]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact mul_nonneg hb0.le (by nlinarith only [hg00, hg01, a0, b0])
    · have hconv : (1 - M.γ0) * d0 + M.γ0 * d1 ≤ 1 := by nlinarith only [hg00, hg01, a1, b1]
      nlinarith only [hb0, hb1, hconv]
    · exact mul_nonneg hb0.le (by nlinarith only [hg10, hg11, b0])
    · have hconv : M.γ1 + (1 - M.γ1) * d1 ≤ 1 := by nlinarith only [hg10, hg11, b1]
      nlinarith only [hb0, hb1, hconv]

private lemma anchorF_slope (M : Params) (hM : M.Standing) (m : ℕ) :
    M.anchorF m 1 - M.anchorF m 0 ≤ M.β := by
  have ⟨hb0, _, _, _, _, _, hg00, hg01, _, _⟩ := hM
  have hbd := prodSeq_diff_bounds M hM (diag 0) (diag 1) (0 + M.cF - M.cR)
    (by simp [diag]) (by simp [diag]) (by simp [diag]) (by simp [diag]) m
  have h1 : 0 + M.cF - M.cR + 1 = 1 + M.cF - M.cR := by ring
  rw [h1] at hbd
  obtain ⟨⟨_, a1⟩, ⟨_, b1⟩⟩ := hbd
  have heq : M.anchorF m 1 - M.anchorF m 0 =
      M.β * ((1 - M.γ0) * ((M.prodSeq (diag 1) (1 + M.cF - M.cR) m) 0 -
            (M.prodSeq (diag 0) (0 + M.cF - M.cR) m) 0) +
          M.γ0 * ((M.prodSeq (diag 1) (1 + M.cF - M.cR) m) 1 -
            (M.prodSeq (diag 0) (0 + M.cF - M.cR) m) 1)) := by
    unfold Params.anchorF dot Params.p0 Params.γ0bar
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  rw [heq]
  have hconv : (1 - M.γ0) * ((M.prodSeq (diag 1) (1 + M.cF - M.cR) m) 0 -
        (M.prodSeq (diag 0) (0 + M.cF - M.cR) m) 0) +
      M.γ0 * ((M.prodSeq (diag 1) (1 + M.cF - M.cR) m) 1 -
        (M.prodSeq (diag 0) (0 + M.cF - M.cR) m) 1) ≤ 1 := by nlinarith only [hg00, hg01, a1, b1]
  nlinarith only [hb0, hconv]

private lemma anchorG_slope (M : Params) (hM : M.Standing) (m : ℕ) :
    M.anchorG m 1 - M.anchorG m 0 ≤ M.β := by
  have ⟨hb0, hb1, _, _, _, _, hg00, hg01, hg10, hg11⟩ := hM
  have hbd := prodSeq_diff_bounds M hM
    (M.inspStart 0 (0 + M.cF - M.cR)) (M.inspStart 1 (1 + M.cF - M.cR))
    (0 + M.cF - M.cR)
    (by simp [Params.inspStart]) (by simp [Params.inspStart])
    (by simp [Params.inspStart, Params.ρ1, Params.γ1bar]; linarith only [hb0])
    (by simp [Params.inspStart, Params.ρ1, Params.γ1bar]; linarith only [hb1]) m
  have h1 : 0 + M.cF - M.cR + 1 = 1 + M.cF - M.cR := by ring
  rw [h1] at hbd
  obtain ⟨⟨_, a1⟩, ⟨_, b1⟩⟩ := hbd
  have heq : M.anchorG m 1 - M.anchorG m 0 =
      M.β * ((1 - M.γ0) * ((M.prodSeq (M.inspStart 1 (1 + M.cF - M.cR)) (1 + M.cF - M.cR) m) 0 -
            (M.prodSeq (M.inspStart 0 (0 + M.cF - M.cR)) (0 + M.cF - M.cR) m) 0) +
          M.γ0 * ((M.prodSeq (M.inspStart 1 (1 + M.cF - M.cR)) (1 + M.cF - M.cR) m) 1 -
            (M.prodSeq (M.inspStart 0 (0 + M.cF - M.cR)) (0 + M.cF - M.cR) m) 1)) := by
    unfold Params.anchorG dot Params.p0 Params.γ0bar
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
  rw [heq]
  have hconv : (1 - M.γ0) * ((M.prodSeq (M.inspStart 1 (1 + M.cF - M.cR)) (1 + M.cF - M.cR) m) 0 -
        (M.prodSeq (M.inspStart 0 (0 + M.cF - M.cR)) (0 + M.cF - M.cR) m) 0) +
      M.γ0 * ((M.prodSeq (M.inspStart 1 (1 + M.cF - M.cR)) (1 + M.cF - M.cR) m) 1 -
        (M.prodSeq (M.inspStart 0 (0 + M.cF - M.cR)) (0 + M.cF - M.cR) m) 1) ≤ 1 := by
    nlinarith only [hg00, hg01, a1, b1]
  nlinarith only [hb0, hconv]

private lemma anchorF_affine (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) (x : ℝ) :
    M.anchorF m x = M.anchorF m 0 + (M.anchorF m 1 - M.anchorF m 0) * x := by
  unfold Params.anchorF dot Params.p0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨c1x, c0x⟩ := prodSeq_closed M hM hγ (diag x) (x + M.cF - M.cR) m
  obtain ⟨c10, c00⟩ := prodSeq_closed M hM hγ (diag 0) (0 + M.cF - M.cR) m
  obtain ⟨c11, c01⟩ := prodSeq_closed M hM hγ (diag 1) (1 + M.cF - M.cR) m
  rw [c0x, c1x, c00, c10, c01, c11]
  simp only [diag, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma anchorG_affine (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) (x : ℝ) :
    M.anchorG m x = M.anchorG m 0 + (M.anchorG m 1 - M.anchorG m 0) * x := by
  unfold Params.anchorG dot Params.p0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨c1x, c0x⟩ := prodSeq_closed M hM hγ (M.inspStart x (x + M.cF - M.cR)) (x + M.cF - M.cR) m
  obtain ⟨c10, c00⟩ := prodSeq_closed M hM hγ (M.inspStart 0 (0 + M.cF - M.cR)) (0 + M.cF - M.cR) m
  obtain ⟨c11, c01⟩ := prodSeq_closed M hM hγ (M.inspStart 1 (1 + M.cF - M.cR)) (1 + M.cF - M.cR) m
  rw [c0x, c1x, c00, c10, c01, c11]
  simp only [Params.inspStart, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma anchorF_sub_self (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) (x : ℝ) :
    M.anchorF m x - x = (1 - (M.anchorF m 1 - M.anchorF m 0)) * (M.f m - x) := by
  have hB : 1 - (M.anchorF m 1 - M.anchorF m 0) ≠ 0 := by
    linarith only [anchorF_slope M hM m, hM.2.1]
  have hf : M.anchorF m 0 = (1 - (M.anchorF m 1 - M.anchorF m 0)) * M.f m := by
    unfold Params.f; field_simp [hB]
  rw [anchorF_affine M hM hγ m x]
  linear_combination hf

private lemma anchorG_sub_self (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) (x : ℝ) :
    M.anchorG m x - x = (1 - (M.anchorG m 1 - M.anchorG m 0)) * (M.g m - x) := by
  have hB : 1 - (M.anchorG m 1 - M.anchorG m 0) ≠ 0 := by
    linarith only [anchorG_slope M hM m, hM.2.1]
  have hg : M.anchorG m 0 = (1 - (M.anchorG m 1 - M.anchorG m 0)) * M.g m := by
    unfold Params.g; field_simp [hB]
  rw [anchorG_affine M hM hγ m x]
  linear_combination hg

private noncomputable def denF (M : Params) (m : ℕ) : ℝ :=
  M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1
    - (1 - M.β) / (M.γ1 - M.γ0)
      * (M.γ1 * M.ρ1bar * M.ρ0 ^ (m + 1) - M.γ0 * M.ρ0bar * M.ρ1 ^ (m + 1))

private noncomputable def denG (M : Params) (m : ℕ) : ℝ :=
  M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1
    + (1 - M.β) / (M.γ1 - M.γ0) * (M.γ0 * M.ρ0bar - M.γ1) * M.ρ1bar * M.ρ0 ^ (m + 1)
    + (1 - M.β) / (M.γ1 - M.γ0) * M.γ0 * M.ρ0bar * M.ρ1 ^ (m + 2)

private lemma denF_pos (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    0 < denF M m := by
  have ⟨_, _, _, _, _, _, _, _, hr0b, hr1b, _, _⟩ := standing_aux M hM
  have h0 : M.ρ0bar ≠ 0 := hr0b.ne'
  have h1 : M.ρ1bar ≠ 0 := hr1b.ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have heq : denF M m = M.ρ0bar * M.ρ1bar * (1 - (M.anchorF m 1 - M.anchorF m 0)) := by
    unfold denF Params.anchorF dot Params.p0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    obtain ⟨c10, c00⟩ := prodSeq_closed M hM hγ (diag 0) (0 + M.cF - M.cR) m
    obtain ⟨c11, c01⟩ := prodSeq_closed M hM hγ (diag 1) (1 + M.cF - M.cR) m
    rw [c00, c10, c01, c11]
    simp only [diag, Matrix.cons_val_zero, Matrix.cons_val_one, pow_succ]
    generalize M.ρ0 ^ m = a
    generalize M.ρ1 ^ m = b
    simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar] at h0 h1 ⊢
    field_simp
    ring
  rw [heq]
  have hB : 0 < 1 - (M.anchorF m 1 - M.anchorF m 0) := by
    linarith only [anchorF_slope M hM m, hM.2.1]
  exact mul_pos (mul_pos hr0b hr1b) hB

private lemma denG_pos (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    0 < denG M m := by
  have ⟨_, _, _, _, _, _, _, _, hr0b, hr1b, _, _⟩ := standing_aux M hM
  have h0 : M.ρ0bar ≠ 0 := hr0b.ne'
  have h1 : M.ρ1bar ≠ 0 := hr1b.ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have heq : denG M m = M.ρ0bar * M.ρ1bar * (1 - (M.anchorG m 1 - M.anchorG m 0)) := by
    unfold denG Params.anchorG dot Params.p0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    obtain ⟨c10, c00⟩ := prodSeq_closed M hM hγ (M.inspStart 0 (0 + M.cF - M.cR)) (0 + M.cF - M.cR) m
    obtain ⟨c11, c01⟩ := prodSeq_closed M hM hγ (M.inspStart 1 (1 + M.cF - M.cR)) (1 + M.cF - M.cR) m
    rw [c00, c10, c01, c11]
    simp only [Params.inspStart, Matrix.cons_val_zero, Matrix.cons_val_one, pow_succ]
    generalize M.ρ0 ^ m = a
    generalize M.ρ1 ^ m = b
    simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar] at h0 h1 ⊢
    field_simp
    ring
  rw [heq]
  have hB : 0 < 1 - (M.anchorG m 1 - M.anchorG m 0) := by
    linarith only [anchorG_slope M hM m, hM.2.1]
  exact mul_pos (mul_pos hr0b hr1b) hB

private lemma f_sub_gInf (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    M.f m - (M.cR + M.uPdot 0) =
      (M.ρ0bar * M.ρ1bar / (M.γ1 - M.γ0)) *
        ((M.γ1 * M.cR - M.γ0 * M.thrP) * M.ρ0 ^ (m + 1) +
          M.γ0 * (M.thrP - M.cR) * M.ρ1 ^ (m + 1)) / denF M m := by
  have ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := standing_aux M hM
  have hden := (denF_pos M hM hγ m).ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have h1b : 1 - M.β ≠ 0 := by linarith only [hM.2.1]
  have hDne : M.D ≠ 0 := hD.ne'
  rw [(lemma_3 M hM hγ m).2]
  unfold Params.f31
  change _ / denF M m - _ = _ / denF M m
  rw [div_sub' hden, div_left_inj' hden]
  unfold denF Params.uPdot Params.thrP
  simp only [Matrix.cons_val_zero]
  generalize M.ρ0 ^ (m + 1) = a
  generalize M.ρ1 ^ (m + 1) = b
  simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar,
    Params.D] at hDne ⊢
  field_simp [hd, h1b, hDne]
  ring

private lemma g_sub_gInf (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    M.g m - (M.cR + M.uPdot 0) =
      (M.ρ0bar * M.ρ1bar / (M.γ1 - M.γ0)) *
        ((M.γ1 * M.cI - M.γ0 * (M.chat / M.D)) * M.ρ0 ^ (m + 1) +
          M.γ0 * (M.chat / M.D - M.cI) * M.ρ1 ^ (m + 1)) / denG M m := by
  have ⟨_, _, _, _, _, _, _, _, _, _, hD, _⟩ := standing_aux M hM
  have hden := (denG_pos M hM hγ m).ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have h1b : 1 - M.β ≠ 0 := by linarith only [hM.2.1]
  have hDne : M.D ≠ 0 := hD.ne'
  rw [(lemma_7 M hM hγ m).2]
  unfold Params.g40
  change _ / denG M m - _ = _ / denG M m
  rw [div_sub' hden, div_left_inj' hden]
  unfold denG Params.a40 Params.uPdot Params.chat
  simp only [Matrix.cons_val_zero]
  have hp0 : M.ρ0 ^ (m + 2) = M.ρ0 ^ (m + 1) * M.ρ0 := pow_succ M.ρ0 (m + 1)
  have hp1 : M.ρ1 ^ (m + 2) = M.ρ1 ^ (m + 1) * M.ρ1 := pow_succ M.ρ1 (m + 1)
  rw [hp0, hp1]
  generalize M.ρ0 ^ (m + 1) = a
  generalize M.ρ1 ^ (m + 1) = b
  simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar,
    Params.D] at hDne ⊢
  field_simp [hd, h1b, hDne]
  ring

private lemma chat_div_D_eq (M : Params) (hM : M.Standing) :
    M.chat / M.D = M.cP + M.β * M.γ1bar * (M.thrP - M.cR) := by
  have hDne : M.D ≠ 0 := (standing_aux M hM).2.2.2.2.2.2.2.2.2.2.1.ne'
  unfold Params.chat Params.thrP
  simp only [Params.γ1bar, Params.D] at hDne ⊢
  field_simp [hDne]
  ring

private lemma param_ineqs (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat) :
    M.γ0 < M.γ1 ∧ M.γ1 * M.cI < M.γ0 * (M.chat / M.D) ∧ M.cI < M.chat / M.D := by
  have ⟨hb0, _, hcP, _, _, _, _, _, hg10, _⟩ := hM
  have ⟨_, _, h1b0, _, _, _, _, _, _, _, _, hthr⟩ := standing_aux M hM
  have hγlt : M.γ0 < M.γ1 := by
    have h1 : M.γ0 / M.γ1 * M.thrP < M.thrP := lt_of_le_of_lt hlo hhi
    have h2 : M.γ0 / M.γ1 < 1 := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h hthr.le
      linarith only [h1, this]
    exact (div_lt_one hg10).mp h2
  set Y := M.chat / M.D
  have hYeq : Y = M.cP + M.β * M.γ1bar * (M.thrP - M.cR) := chat_div_D_eq M hM
  have hYpos : 0 < Y := by
    rw [hYeq]
    exact add_pos hcP (mul_pos (mul_pos hb0 h1b0) (sub_pos.mpr hhi))
  have hcI' : M.γ1 * M.cI < M.γ0 * Y := by
    have h1 : M.γ0 / M.γ1 * (1 / M.D) * M.chat = M.γ0 * Y / M.γ1 := by simp only [Y]; ring
    rw [h1, lt_div_iff₀ hg10] at hcI
    linarith only [hcI]
  have hYcI : M.cI < Y := by
    have h1 : M.γ0 * Y < M.γ1 * Y := mul_lt_mul_of_pos_right hγlt hYpos
    have h2 : M.γ1 * M.cI < M.γ1 * Y := lt_trans hcI' h1
    exact lt_of_mul_lt_mul_left h2 hg10.le
  exact ⟨hγlt, hcI', hYcI⟩

private lemma g_tendsto_gInf (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) :
    Tendsto M.g atTop (𝓝 (M.cR + M.uPdot 0)) := by
  have ⟨_, _, _, _, hr00, hr01, hr10, hr11, _, _, hD, _⟩ := standing_aux M hM
  have ht0 : Tendsto (fun m : ℕ => M.ρ0 ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr00.le hr01).comp (tendsto_add_atTop_nat 1)
  have ht1 : Tendsto (fun m : ℕ => M.ρ1 ^ (m + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr10.le hr11).comp (tendsto_add_atTop_nat 1)
  have ht1_2 : Tendsto (fun m : ℕ => M.ρ1 ^ (m + 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr10.le hr11).comp (tendsto_add_atTop_nat 2)
  set c0 := M.γ1 * M.cI - M.γ0 * (M.chat / M.D)
  set c1 := M.γ0 * (M.chat / M.D - M.cI)
  set fac := M.ρ0bar * M.ρ1bar / (M.γ1 - M.γ0)
  have hnum : Tendsto (fun m : ℕ => fac * (c0 * M.ρ0 ^ (m + 1) + c1 * M.ρ1 ^ (m + 1)))
      atTop (𝓝 0) := by
    have h := ((ht0.const_mul c0).add (ht1.const_mul c1)).const_mul fac
    simpa using h
  have hden_lim : M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1 = (1 - M.β) * M.D := by
    unfold Params.ρ0bar Params.ρ1bar Params.ρ0 Params.ρ1 Params.γ0bar Params.γ1bar Params.D
    ring
  have hden_pos : 0 < M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1 := by
    rw [hden_lim]
    exact mul_pos (by linarith only [hM.2.1]) hD
  set d0 := (1 - M.β) / (M.γ1 - M.γ0) * (M.γ0 * M.ρ0bar - M.γ1) * M.ρ1bar
  set d1 := (1 - M.β) / (M.γ1 - M.γ0) * M.γ0 * M.ρ0bar
  have hden : Tendsto (denG M) atTop (𝓝 (M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1)) := by
    have hdeq : denG M = fun m =>
        (M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1) + d0 * M.ρ0 ^ (m + 1) + d1 * M.ρ1 ^ (m + 2) := by
      funext m; unfold denG; simp only [d0, d1]
    rw [hdeq]
    have h := ((tendsto_const_nhds (x := M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1)).add
      (ht0.const_mul d0)).add (ht1_2.const_mul d1)
    simpa using h
  have hdiff : Tendsto (fun m => M.g m - (M.cR + M.uPdot 0)) atTop (𝓝 0) := by
    have h := hnum.div hden hden_pos.ne'
    simp only [zero_div] at h
    exact h.congr (fun m => (g_sub_gInf M hM hγ m).symm)
  have hadd := hdiff.add_const (M.cR + M.uPdot 0)
  simpa using hadd

private lemma exists_min_g (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat) :
    ∃ mstar : ℕ, (∀ m, M.g mstar ≤ M.g m) ∧ M.g mstar < M.cR + M.uPdot 0 := by
  have ⟨hb0, _, _, _, _, _, _, _, _, _⟩ := hM
  have ⟨_, _, _, _, hr00, _, hr10, _, hr0b, hr1b, _, _⟩ := standing_aux M hM
  have ⟨hγlt, hcI', hYcI⟩ := param_ineqs M hM hlo hhi hcI
  have hγ : M.γ0 ≠ M.γ1 := hγlt.ne
  have hd : 0 < M.γ1 - M.γ0 := sub_pos.mpr hγlt
  set Y := M.chat / M.D
  have hrlt : M.ρ1 / M.ρ0 < 1 := by
    rw [div_lt_one hr00]
    unfold Params.ρ0 Params.ρ1 Params.γ0bar Params.γ1bar
    nlinarith only [hb0, hγlt]
  have hrat_lim : Tendsto (fun m : ℕ =>
      (M.γ1 * M.cI - M.γ0 * Y) + M.γ0 * (Y - M.cI) * (M.ρ1 / M.ρ0) ^ (m + 1))
      atTop (𝓝 (M.γ1 * M.cI - M.γ0 * Y)) := by
    have ht : Tendsto (fun m : ℕ => (M.ρ1 / M.ρ0) ^ (m + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr10.le hr00.le) hrlt).comp
        (tendsto_add_atTop_nat 1)
    have h := (tendsto_const_nhds (x := M.γ1 * M.cI - M.γ0 * Y)).add
      (ht.const_mul (M.γ0 * (Y - M.cI)))
    simpa using h
  have hev_neg : ∀ᶠ m in atTop,
      (M.γ1 * M.cI - M.γ0 * Y) + M.γ0 * (Y - M.cI) * (M.ρ1 / M.ρ0) ^ (m + 1) < 0 :=
    hrat_lim.eventually (Iio_mem_nhds (sub_neg.mpr hcI'))
  obtain ⟨m0, hm0_neg⟩ := hev_neg.exists
  have hm0_lt : M.g m0 < M.cR + M.uPdot 0 := by
    have hsub := g_sub_gInf M hM hγ m0
    have hden := denG_pos M hM hγ m0
    have hr0pow : 0 < M.ρ0 ^ (m0 + 1) := pow_pos hr00 (m0 + 1)
    have hfac : 0 < M.ρ0bar * M.ρ1bar / (M.γ1 - M.γ0) := div_pos (mul_pos hr0b hr1b) hd
    have hnum_eq :
        (M.γ1 * M.cI - M.γ0 * Y) * M.ρ0 ^ (m0 + 1) + M.γ0 * (Y - M.cI) * M.ρ1 ^ (m0 + 1) =
        ((M.γ1 * M.cI - M.γ0 * Y) + M.γ0 * (Y - M.cI) * (M.ρ1 / M.ρ0) ^ (m0 + 1)) *
          M.ρ0 ^ (m0 + 1) := by
      rw [div_pow]
      field_simp [hr0pow.ne']
    have hnum_neg :
        (M.γ1 * M.cI - M.γ0 * Y) * M.ρ0 ^ (m0 + 1) + M.γ0 * (Y - M.cI) * M.ρ1 ^ (m0 + 1) < 0 := by
      rw [hnum_eq]
      exact mul_neg_of_neg_of_pos hm0_neg hr0pow
    have hquot_neg : M.g m0 - (M.cR + M.uPdot 0) < 0 := by
      rw [hsub]
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hfac hnum_neg) hden
    linarith only [hquot_neg]
  have hev_gt : ∀ᶠ m in atTop, M.g m0 < M.g m :=
    (g_tendsto_gInf M hM hγ).eventually (Ioi_mem_nhds hm0_lt)
  rw [Filter.eventually_atTop] at hev_gt
  obtain ⟨N, hN⟩ := hev_gt
  set K := max N (m0 + 1)
  have hm0_in : m0 ∈ Finset.range K :=
    Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self m0) (le_max_right N (m0 + 1)))
  obtain ⟨mstar, _, hmstar_min⟩ := Finset.exists_min_image (Finset.range K) M.g ⟨m0, hm0_in⟩
  have hmstar_le_m0 : M.g mstar ≤ M.g m0 := hmstar_min m0 hm0_in
  refine ⟨mstar, ?_, lt_of_le_of_lt hmstar_le_m0 hm0_lt⟩
  intro m
  by_cases hm : m < K
  · exact hmstar_min m (Finset.mem_range.mpr hm)
  · have hge : N ≤ m := le_trans (le_max_left N (m0 + 1)) (Nat.le_of_not_lt hm)
    exact le_trans hmstar_le_m0 (hN m hge).le

private lemma pir_coord_bounds (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat)
    (mstar : ℕ) (hmstar_min : ∀ m, M.g mstar ≤ M.g m)
    (hmstar_lt : M.g mstar < M.cR + M.uPdot 0) :
    let uR0 := M.g mstar
    let uF := uR0 + M.cF - M.cR
    let K := M.cP + M.β * M.γ1 * uF
    let uR := M.prodSeq (diag uR0) uF
    let uI := M.prodSeq (M.inspStart uR0 uF) uF
    (∀ i, uR0 ≤ M.cR + M.β * dot M.p0 (uI i)) ∧
    (M.cR + M.β * dot M.p0 (uI mstar) = uR0) ∧
    (∀ j, uR0 ≤ M.cR + M.β * dot M.p0 (uR j)) ∧
    (∀ j, uR0 ≤ (uR j) 1) ∧
    (∀ i, uR0 ≤ (uI i) 1) ∧
    (uI (mstar + 1)) 0 < M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar) ∧
    (uI (mstar + 1)) 1 < K / M.ρ1bar := by
  have ⟨_, hb1, _, hPI, _, _, hg00, _, hg10, _⟩ := hM
  have ⟨_, _, _, _, hr00, _, hr10, hr11, hr0b, hr1b, hD, _⟩ := standing_aux M hM
  have ⟨hγlt, _, hYcI⟩ := param_ineqs M hM hlo hhi hcI
  have hγ : M.γ0 ≠ M.γ1 := hγlt.ne
  have hd : 0 < M.γ1 - M.γ0 := sub_pos.mpr hγlt
  set uR0 := M.g mstar
  set gInf := M.cR + M.uPdot 0
  set δ := gInf - uR0
  have hδ : 0 < δ := sub_pos.mpr hmstar_lt
  set uF := uR0 + M.cF - M.cR
  set K := M.cP + M.β * M.γ1 * uF
  set uR : ℕ → Vec := M.prodSeq (diag uR0) uF
  set uI : ℕ → Vec := M.prodSeq (M.inspStart uR0 uF) uF
  set uInf0 : ℝ := M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar)
  set uInf1 : ℝ := K / M.ρ1bar
  have h1b : 1 - M.β ≠ 0 := by linarith only [hb1]
  have hDne : M.D ≠ 0 := hD.ne'
  have hr0bne : M.ρ0bar ≠ 0 := hr0b.ne'
  have hr1bne : M.ρ1bar ≠ 0 := hr1b.ne'
  -- f(j) > uR0 for all j
  have hf_gt : ∀ j : ℕ, uR0 < M.f j := by
    intro j
    have hfj := f_sub_gInf M hM hγ j
    have hden := denF_pos M hM hγ j
    have hfac : 0 < M.ρ0bar * M.ρ1bar / (M.γ1 - M.γ0) := div_pos (mul_pos hr0b hr1b) hd
    have h1 : 0 ≤ M.γ1 * M.cR - M.γ0 * M.thrP := by
      have : M.γ0 * M.thrP / M.γ1 ≤ M.cR := by
        simpa [mul_div_assoc, div_mul_eq_mul_div] using hlo
      rw [div_le_iff₀ hg10] at this
      linarith only [this]
    have h2 : 0 < M.γ0 * (M.thrP - M.cR) * M.ρ1 ^ (j + 1) :=
      mul_pos (mul_pos hg00 (sub_pos.mpr hhi)) (pow_pos hr10 (j + 1))
    have h0 : 0 ≤ (M.γ1 * M.cR - M.γ0 * M.thrP) * M.ρ0 ^ (j + 1) :=
      mul_nonneg h1 (pow_nonneg hr00.le (j + 1))
    have hnum : 0 < (M.γ1 * M.cR - M.γ0 * M.thrP) * M.ρ0 ^ (j + 1) +
        M.γ0 * (M.thrP - M.cR) * M.ρ1 ^ (j + 1) := by linarith only [h0, h2]
    have hgt : 0 < M.f j - gInf := by
      rw [hfj]; exact div_pos (mul_pos hfac hnum) hden
    linarith only [hmstar_lt, hgt]
  -- Anchor inequalities at p0
  have hp0_uI : ∀ i : ℕ, uR0 ≤ M.cR + M.β * dot M.p0 (uI i) := by
    intro i
    have hsub := anchorG_sub_self M hM hγ i uR0
    have hB : 0 < 1 - (M.anchorG i 1 - M.anchorG i 0) := by
      linarith only [anchorG_slope M hM i, hb1]
    have hnn : 0 ≤ M.anchorG i uR0 - uR0 := by
      rw [hsub]; exact mul_nonneg hB.le (sub_nonneg.mpr (hmstar_min i))
    change uR0 ≤ M.anchorG i uR0
    linarith only [hnn]
  have hp0_uI_eq : M.cR + M.β * dot M.p0 (uI mstar) = uR0 := by
    have hsub := anchorG_sub_self M hM hγ mstar uR0
    have hz : M.anchorG mstar uR0 - uR0 = 0 := by rw [hsub]; simp only [uR0, sub_self, mul_zero]
    change M.anchorG mstar uR0 = uR0
    linarith only [hz]
  have hp0_uR : ∀ j : ℕ, uR0 ≤ M.cR + M.β * dot M.p0 (uR j) := by
    intro j
    have hsub := anchorF_sub_self M hM hγ j uR0
    have hB : 0 < 1 - (M.anchorF j 1 - M.anchorF j 0) := by
      linarith only [anchorF_slope M hM j, hb1]
    have hnn : 0 ≤ M.anchorF j uR0 - uR0 := by
      rw [hsub]; exact mul_nonneg hB.le (sub_nonneg.mpr (hf_gt j).le)
    change uR0 ≤ M.anchorF j uR0
    linarith only [hnn]
  -- Algebraic identities in terms of δ
  have huR0_eq : uR0 = gInf - δ := by simp only [δ]; ring
  have huInf1_gt_uR0 : uR0 < uInf1 := by
    have heq : uInf1 - uR0 = (M.thrP - M.cR) + (1 - M.β) / M.ρ1bar * δ := by
      simp only [uInf1, K, uF, huR0_eq, gInf, Params.uPdot, Params.thrP, Matrix.cons_val_zero]
      simp only [Params.ρ1bar, Params.ρ1, Params.γ1bar, Params.D] at hDne hr1bne ⊢
      field_simp [h1b, hDne, hr1bne]
      ring
    have h1 : 0 < M.thrP - M.cR := sub_pos.mpr hhi
    have h2 : 0 < (1 - M.β) / M.ρ1bar * δ := mul_pos (div_pos (by linarith only [hb1]) hr1b) hδ
    linarith only [heq, h1, h2]
  have huI01_gt_uR0 : uR0 < (uI 0) 1 := by
    have heq : (uI 0) 1 - uR0 = (M.cI - M.cP) + M.ρ1bar * (M.thrP - M.cR) + (1 - M.β) * δ := by
      simp only [uI, Params.prodSeq, Params.inspStart, Matrix.cons_val_one, uF, huR0_eq, gInf,
        Params.uPdot, Params.thrP, Matrix.cons_val_zero]
      simp only [Params.ρ1bar, Params.ρ1, Params.γ1bar, Params.D] at hDne ⊢
      field_simp [h1b, hDne]
      ring
    have h1 : 0 < M.cI - M.cP := sub_pos.mpr hPI
    have h2 : 0 < M.ρ1bar * (M.thrP - M.cR) := mul_pos hr1b (sub_pos.mpr hhi)
    have h3 : 0 < (1 - M.β) * δ := mul_pos (by linarith only [hb1]) hδ
    linarith only [heq, h1, h2, h3]
  have huInf1_gt_uI01 : (uI 0) 1 < uInf1 := by
    have heq : uInf1 - (uI 0) 1 = (M.chat / M.D - M.cI) + (1 - M.β) * M.ρ1 / M.ρ1bar * δ := by
      simp only [uInf1, K, uI, Params.prodSeq, Params.inspStart, Matrix.cons_val_one, uF, huR0_eq,
        gInf, Params.uPdot, Params.chat, Matrix.cons_val_zero]
      simp only [Params.ρ1bar, Params.ρ1, Params.γ1bar, Params.D] at hDne hr1bne ⊢
      field_simp [h1b, hDne, hr1bne]
      ring
    have h1 : 0 < M.chat / M.D - M.cI := sub_pos.mpr hYcI
    have h2 : 0 < (1 - M.β) * M.ρ1 / M.ρ1bar * δ :=
      mul_pos (div_pos (mul_pos (by linarith only [hb1]) hr10) hr1b) hδ
    linarith only [heq, h1, h2]
  -- Coordinate 1 bounds
  have huR_coord1 : ∀ j : ℕ, uR0 ≤ (uR j) 1 := by
    intro j
    have hc := (prodSeq_closed M hM hγ (diag uR0) uF j).1
    have hd1 : diag uR0 1 = uR0 := rfl
    change uR0 ≤ (M.prodSeq (diag uR0) uF j) 1
    rw [hc, hd1]
    have hpow : M.ρ1 ^ j ≤ 1 := pow_le_one₀ hr10.le hr11.le
    have hdiff : 0 ≤ (uInf1 - uR0) * (1 - M.ρ1 ^ j) :=
      mul_nonneg (sub_nonneg.mpr huInf1_gt_uR0.le) (sub_nonneg.mpr hpow)
    change uR0 ≤ (uR0 - uInf1) * M.ρ1 ^ j + uInf1
    linarith only [hdiff]
  have huI_coord1 : ∀ i : ℕ, uR0 ≤ (uI i) 1 := by
    intro i
    have hc := (prodSeq_closed M hM hγ (M.inspStart uR0 uF) uF i).1
    have h1 : (M.inspStart uR0 uF) 1 = (uI 0) 1 := rfl
    change uR0 ≤ (M.prodSeq (M.inspStart uR0 uF) uF i) 1
    rw [hc, h1]
    have hpow : M.ρ1 ^ i ≤ 1 := pow_le_one₀ hr10.le hr11.le
    have hdiff : 0 ≤ (uInf1 - (uI 0) 1) * (1 - M.ρ1 ^ i) :=
      mul_nonneg (sub_nonneg.mpr huInf1_gt_uI01.le) (sub_nonneg.mpr hpow)
    change uR0 ≤ ((uI 0) 1 - uInf1) * M.ρ1 ^ i + uInf1
    linarith only [huI01_gt_uR0, hdiff]
  -- Strict domination of uInf by uI (mstar + 1)
  have huInf0_gt_uIm1 : (uI (mstar + 1)) 0 < uInf0 := by
    have hc0 : (uI (mstar + 1)) 0 = uR0 - M.cR := by
      have hs := (prodSeq_step M (M.inspStart uR0 uF) uF mstar).1
      change (M.prodSeq (M.inspStart uR0 uF) uF (mstar + 1)) 0 = uR0 - M.cR
      rw [hs]
      linarith only [hp0_uI_eq]
    rw [hc0]
    have hdiff : uInf0 - (uR0 - M.cR) = (1 - M.β) * M.D / (M.ρ0bar * M.ρ1bar) * δ := by
      simp only [uInf0, K, uF, huR0_eq, gInf, Params.uPdot, Matrix.cons_val_zero]
      simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar,
        Params.D] at hDne hr0bne hr1bne ⊢
      field_simp [h1b, hDne, hr0bne, hr1bne]
      ring
    have hpos : 0 < (1 - M.β) * M.D / (M.ρ0bar * M.ρ1bar) * δ :=
      mul_pos (div_pos (mul_pos (by linarith only [hb1]) hD) (mul_pos hr0b hr1b)) hδ
    linarith only [hdiff, hpos]
  have huInf1_gt_uIm1 : (uI (mstar + 1)) 1 < uInf1 := by
    have hc := (prodSeq_closed M hM hγ (M.inspStart uR0 uF) uF (mstar + 1)).1
    have h1 : (M.inspStart uR0 uF) 1 = (uI 0) 1 := rfl
    change (M.prodSeq (M.inspStart uR0 uF) uF (mstar + 1)) 1 < uInf1
    rw [hc, h1]
    have hpos : 0 < (uInf1 - (uI 0) 1) * M.ρ1 ^ (mstar + 1) :=
      mul_pos (sub_pos.mpr huInf1_gt_uI01) (pow_pos hr10 (mstar + 1))
    change ((uI 0) 1 - uInf1) * M.ρ1 ^ (mstar + 1) + uInf1 < uInf1
    linarith only [hpos]
  exact ⟨hp0_uI, hp0_uI_eq, hp0_uR, huR_coord1, huI_coord1, huInf0_gt_uIm1, huInf1_gt_uIm1⟩

private lemma dot_PP_adj (M : Params) (uF : ℝ) (π u : Vec) :
    dot π (M.gP uF) + M.β * dot (M.PPt π) u = dot π (M.gP uF + M.β • M.PP u) := by
  simp only [dot, Params.gP, Params.PPt, Params.PP, Params.p0, Params.p1,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma dot_le_of_coord_le (π u v : Vec) (hπ0 : 0 ≤ π 0) (hπ1 : 0 ≤ π 1)
    (h0 : u 0 ≤ v 0) (h1 : u 1 ≤ v 1) : dot π u ≤ dot π v := by
  unfold dot
  exact add_le_add (mul_le_mul_of_nonneg_left h0 hπ0) (mul_le_mul_of_nonneg_left h1 hπ1)

private lemma minDot_le_of_mem {U : Finset Vec} {u : Vec} (hu : u ∈ U) (π : Vec) :
    minDot U π ≤ dot π u := by
  have hne : U.Nonempty := ⟨u, hu⟩
  unfold minDot
  rw [dif_pos hne]
  exact Finset.inf'_le _ hu

private lemma le_minDot {U : Finset Vec} (hU : U.Nonempty) (π : Vec) (x : ℝ)
    (h : ∀ u ∈ U, x ≤ dot π u) : x ≤ minDot U π := by
  unfold minDot
  rw [dif_pos hU]
  exact Finset.le_inf' hU _ h

private lemma exists_mem_minDot {U : Finset Vec} (hU : U.Nonempty) (π : Vec) :
    ∃ u ∈ U, minDot U π = dot π u := by
  unfold minDot
  rw [dif_pos hU]
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_inf' hU (dot π)
  exact ⟨u, hu, heq⟩

private lemma pir_main (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat) :
    M.PIRStructure := by
  have hb0 : 0 < M.β := hM.1
  have h1b0 : 0 < M.γ1bar := (standing_aux M hM).2.2.1
  have hγ : M.γ0 ≠ M.γ1 := (param_ineqs M hM hlo hhi hcI).1.ne
  obtain ⟨mstar, hmstar_min, hmstar_lt⟩ := exists_min_g M hM hlo hhi hcI
  set uR0 := M.g mstar
  set uF := uR0 + M.cF - M.cR
  set uR : ℕ → Vec := M.prodSeq (diag uR0) uF
  set uI : ℕ → Vec := M.prodSeq (M.inspStart uR0 uF) uF
  obtain ⟨hp0_uI, hp0_uI_eq, hp0_uR, huR_coord1, huI_coord1, huInf0_gt, huInf1_gt⟩ :=
    pir_coord_bounds M hM hlo hhi hcI mstar hmstar_min hmstar_lt
  obtain ⟨htR0, htR1⟩ := prodSeq_tendsto M hM hγ (diag uR0) uF
  obtain ⟨htI0, htI1⟩ := prodSeq_tendsto M hM hγ (M.inspStart uR0 uF) uF
  have hevR : ∀ᶠ k in atTop,
      (uI (mstar + 1)) 0 < (uR (k + 1)) 0 ∧ (uI (mstar + 1)) 1 < (uR (k + 1)) 1 :=
    ((htR0.comp (tendsto_add_atTop_nat 1)).eventually (Ioi_mem_nhds huInf0_gt)).and
      ((htR1.comp (tendsto_add_atTop_nat 1)).eventually (Ioi_mem_nhds huInf1_gt))
  obtain ⟨nR, hnR0, hnR1⟩ := hevR.exists
  have hevI : ∀ᶠ k in atTop,
      (mstar + 1 ≤ k) ∧
      ((uI (mstar + 1)) 0 < (uI (k + 1)) 0 ∧ (uI (mstar + 1)) 1 < (uI (k + 1)) 1) :=
    (eventually_ge_atTop (mstar + 1)).and
      (((htI0.comp (tendsto_add_atTop_nat 1)).eventually (Ioi_mem_nhds huInf0_gt)).and
        ((htI1.comp (tendsto_add_atTop_nat 1)).eventually (Ioi_mem_nhds huInf1_gt)))
  obtain ⟨nI, hnI_ge, hnI0, hnI1⟩ := hevI.exists
  refine ⟨mstar, hmstar_min, nR, nI, ?_⟩
  set U := M.UPIR mstar nR nI
  have mem_uR : ∀ j ≤ nR, uR j ∈ U := fun j hj =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩)
  have mem_uI : ∀ i ≤ nI, uI i ∈ U := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩)
  have hU_ne : U.Nonempty := ⟨uR 0, mem_uR 0 (Nat.zero_le nR)⟩
  have hmstar_le_nI : mstar ≤ nI := le_trans (Nat.le_succ mstar) hnI_ge
  have hWp0 : M.cR + M.β * minDot U M.p0 = uR0 := by
    apply le_antisymm
    · have hle : minDot U M.p0 ≤ dot M.p0 (uI mstar) :=
        minDot_le_of_mem (mem_uI mstar hmstar_le_nI) M.p0
      have hmul := mul_le_mul_of_nonneg_left hle hb0.le
      linarith only [hmul, hp0_uI_eq]
    · have hge : (uR0 - M.cR) / M.β ≤ minDot U M.p0 := by
        apply le_minDot hU_ne
        intro u hu
        rcases Finset.mem_union.mp hu with hR | hI
        · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hR
          rw [div_le_iff₀ hb0]
          linarith only [hp0_uR j]
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI
          rw [div_le_iff₀ hb0]
          linarith only [hp0_uI i]
      have hmul := mul_le_mul_of_nonneg_left hge hb0.le
      rw [mul_div_cancel₀ _ hb0.ne'] at hmul
      linarith only [hmul]
  have hF : M.cF + M.β * minDot U M.p0 = uF := by
    simp only [uF]; linarith only [hWp0]
  have hWp1 : minDot U M.p1 = M.γ1bar * uR0 := by
    apply le_antisymm
    · have hle := minDot_le_of_mem (mem_uR 0 (Nat.zero_le nR)) M.p1
      have h0 : dot M.p1 (uR 0) = M.γ1bar * uR0 := by
        simp [uR, Params.prodSeq, diag, dot, Params.p1]
      linarith only [hle, h0]
    · apply le_minDot hU_ne
      intro u hu
      have hdot : dot M.p1 u = M.γ1bar * u 1 := by simp [dot, Params.p1]
      rw [hdot]
      apply mul_le_mul_of_nonneg_left _ h1b0.le
      rcases Finset.mem_union.mp hu with hR | hI
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hR
        exact huR_coord1 j
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI
        exact huI_coord1 i
  refine solves_of_bellman_fixed_point M hM ActSet.PIR U hU_ne uF ?_ hF
  intro π hπ0 hπ1
  simp only [Params.bellman]
  have htR : (π 0 + π 1) * (M.cR + M.β * minDot U M.p0) = dot π (uR 0) := by
    rw [hWp0]
    simp [uR, Params.prodSeq, diag, dot]
    ring
  have htI : dot π (M.gI uF) + M.β * (π 0 * minDot U M.p0 + π 1 * minDot U M.p1) =
      dot π (uI 0) := by
    have hbm : M.β * minDot U M.p0 = uR0 - M.cR := by linarith only [hWp0]
    rw [hWp1]
    simp only [dot, Params.gI, uI, Params.prodSeq, Params.inspStart, Params.ρ1,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination π 0 * hbm
  rw [htR, htI]
  set tP := dot π (M.gP uF) + M.β * minDot U (M.PPt π)
  apply le_antisymm
  · apply le_minDot hU_ne
    intro u hu
    rcases Finset.mem_union.mp hu with hR | hI
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hR
      cases j with
      | zero => exact le_trans (min_le_left _ _) (min_le_right _ _)
      | succ j' =>
        have hj' : j' ≤ nR := Nat.le_of_succ_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        have hstep : uR (j' + 1) = M.gP uF + M.β • M.PP (uR j') := rfl
        have hle : tP ≤ dot π (uR (j' + 1)) := by
          rw [hstep, ← dot_PP_adj]
          have hmul := mul_le_mul_of_nonneg_left (minDot_le_of_mem (mem_uR j' hj') (M.PPt π)) hb0.le
          linarith only [hmul]
        exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hle)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hI
      cases i with
      | zero => exact min_le_right _ _
      | succ i' =>
        have hi' : i' ≤ nI := Nat.le_of_succ_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        have hstep : uI (i' + 1) = M.gP uF + M.β • M.PP (uI i') := rfl
        have hle : tP ≤ dot π (uI (i' + 1)) := by
          rw [hstep, ← dot_PP_adj]
          have hmul := mul_le_mul_of_nonneg_left (minDot_le_of_mem (mem_uI i' hi') (M.PPt π)) hb0.le
          linarith only [hmul]
        exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) hle)
  · refine le_min (le_min ?_ (minDot_le_of_mem (mem_uR 0 (Nat.zero_le nR)) π))
      (minDot_le_of_mem (mem_uI 0 (Nat.zero_le nI)) π)
    obtain ⟨u, hu, heq⟩ := exists_mem_minDot hU_ne (M.PPt π)
    have htP_eq : tP = dot π (M.gP uF + M.β • M.PP u) := by
      simp only [tP, heq, dot_PP_adj]
    rw [htP_eq]
    rcases Finset.mem_union.mp hu with hR | hI
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hR
      have hj_le : j ≤ nR := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      change minDot U π ≤ dot π (uR (j + 1))
      by_cases hlt : j < nR
      · exact minDot_le_of_mem (mem_uR (j + 1) hlt) π
      · have hjeq : j = nR := le_antisymm hj_le (Nat.le_of_not_lt hlt)
        rw [hjeq]
        exact le_trans (minDot_le_of_mem (mem_uI (mstar + 1) hnI_ge) π)
          (dot_le_of_coord_le π _ _ hπ0 hπ1 hnR0.le hnR1.le)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hI
      have hi_le : i ≤ nI := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      change minDot U π ≤ dot π (uI (i + 1))
      by_cases hlt : i < nI
      · exact minDot_le_of_mem (mem_uI (i + 1) hlt) π
      · have hieq : i = nI := le_antisymm hi_le (Nat.le_of_not_lt hlt)
        rw [hieq]
        exact le_trans (minDot_le_of_mem (mem_uI (mstar + 1) hnI_ge) π)
          (dot_le_of_coord_le π _ _ hπ0 hπ1 hnI0.le hnI1.le)

end Helpers

end MaintPOMDP.Frontier

open MaintPOMDP.Frontier in
theorem solution (M : Params) (hM : M.Standing)
    (hlo : M.γ0 / M.γ1 * M.thrP ≤ M.cR) (hhi : M.cR < M.thrP)
    (hcI : M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat) :
    M.PIRStructure :=
  pir_main M hM hlo hhi hcI
