-- Prove2me | solution 1 for MaintPOMDP.Frontier.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:09:38.529297+00:00
-- url     : https://prove2.me/submissions/238fe696-203e-41c4-b1dc-94ff9fcd6550

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting

set_option autoImplicit false
open Filter Topology

namespace MaintPOMDP.Frontier

lemma qqE_prod_step (M : Params) (u0 : Vec) (uF : ℝ) (i : ℕ) :
    (M.prodSeq u0 uF (i + 1)) 0 = M.β * (M.γ0bar * (M.prodSeq u0 uF i) 0 + M.γ0 * (M.prodSeq u0 uF i) 1) ∧
    (M.prodSeq u0 uF (i + 1)) 1 =
      (M.cP + M.β * M.γ1 * uF) + M.β * (M.γ1bar * (M.prodSeq u0 uF i) 1) := by
  constructor
  · simp [Params.prodSeq, Params.gP, Params.PP, dot, Params.p0, Params.p1]
  · simp [Params.prodSeq, Params.gP, Params.PP, dot, Params.p0, Params.p1]

lemma qqE_prod_closed (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (u0 : Vec) (uF : ℝ)
    (i : ℕ) :
    let K := M.cP + M.β * M.γ1 * uF
    (M.prodSeq u0 uF i) 1 = (u0 1 - K / M.ρ1bar) * M.ρ1 ^ i + K / M.ρ1bar ∧
    (M.prodSeq u0 uF i) 0 =
      (u0 0 - M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar) + M.γ0 / (M.γ1 - M.γ0) * (u0 1 - K / M.ρ1bar))
        * M.ρ0 ^ i
      - M.γ0 / (M.γ1 - M.γ0) * (u0 1 - K / M.ρ1bar) * M.ρ1 ^ i
      + M.β * M.γ0 * K / (M.ρ0bar * M.ρ1bar) := by
  obtain ⟨hb0, hb1, hcP, -, -, -, hg0, hg0', hg1, hg1'⟩ := hM
  have h0 : M.ρ0bar ≠ 0 := by
    have : 0 < M.ρ0bar := by unfold Params.ρ0bar Params.ρ0 Params.γ0bar; nlinarith
    exact this.ne'
  have h1 : M.ρ1bar ≠ 0 := by
    have : 0 < M.ρ1bar := by unfold Params.ρ1bar Params.ρ1 Params.γ1bar; nlinarith
    exact this.ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  unfold Params.ρ0bar Params.ρ1bar Params.ρ0 Params.ρ1 Params.γ0bar Params.γ1bar at *
  induction i with
  | zero =>
    simp only [Params.prodSeq, pow_zero, mul_one]
    constructor
    · ring
    · field_simp
      ring
  | succ i ih =>
    obtain ⟨ih1, ih0⟩ := ih
    obtain ⟨s0, s1⟩ := qqE_prod_step M u0 uF i
    simp only [Params.γ0bar, Params.γ1bar] at s0 s1
    rw [s0, s1, ih0, ih1]
    simp only [pow_succ]
    constructor
    · field_simp
      ring
    · field_simp
      ring


noncomputable def anchorCF (M : Params) (m : ℕ) (x : ℝ) : ℝ :=
  M.cR + M.β * (M.γ0bar * ((x - M.β*M.γ0*(M.cP + M.β*M.γ1*(x+M.cF-M.cR))/(M.ρ0bar*M.ρ1bar)
      + M.γ0/(M.γ1-M.γ0)*(x - (M.cP + M.β*M.γ1*(x+M.cF-M.cR))/M.ρ1bar))*M.ρ0^m
      - M.γ0/(M.γ1-M.γ0)*(x - (M.cP + M.β*M.γ1*(x+M.cF-M.cR))/M.ρ1bar)*M.ρ1^m
      + M.β*M.γ0*(M.cP + M.β*M.γ1*(x+M.cF-M.cR))/(M.ρ0bar*M.ρ1bar))
    + M.γ0 * ((x - (M.cP + M.β*M.γ1*(x+M.cF-M.cR))/M.ρ1bar)*M.ρ1^m + (M.cP + M.β*M.γ1*(x+M.cF-M.cR))/M.ρ1bar))

lemma vvF_anchor_cf (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) (x : ℝ) :
    M.anchorF m x = anchorCF M m x := by
  obtain ⟨c1, c0⟩ := qqE_prod_closed M hM hγ (diag x) (x + M.cF - M.cR) m
  unfold Params.anchorF dot Params.p0 anchorCF
  simp only [diag, Matrix.cons_val_zero, Matrix.cons_val_one] at c0 c1 ⊢
  rw [c0, c1]

lemma vvF_slope (M : Params) (hM : M.Standing) (m : ℕ) :
    M.anchorF m 1 - M.anchorF m 0 ≤ M.β := by
  obtain ⟨hb0, hb1, hcP, -, -, -, hg0, hg0', hg1, hg1'⟩ := hM
  have inv : ∀ i : ℕ,
      (0 ≤ M.prodSeq (diag 1) (1 + M.cF - M.cR) i 0 - M.prodSeq (diag 0) (0 + M.cF - M.cR) i 0 ∧
       M.prodSeq (diag 1) (1 + M.cF - M.cR) i 0 - M.prodSeq (diag 0) (0 + M.cF - M.cR) i 0 ≤ 1) ∧
      (0 ≤ M.prodSeq (diag 1) (1 + M.cF - M.cR) i 1 - M.prodSeq (diag 0) (0 + M.cF - M.cR) i 1 ∧
       M.prodSeq (diag 1) (1 + M.cF - M.cR) i 1 - M.prodSeq (diag 0) (0 + M.cF - M.cR) i 1 ≤ 1) := by
    intro i
    induction i with
    | zero => simp [Params.prodSeq, diag]
    | succ i ih =>
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := ih
      obtain ⟨s0, s1⟩ := qqE_prod_step M (diag 1) (1 + M.cF - M.cR) i
      obtain ⟨t0, t1⟩ := qqE_prod_step M (diag 0) (0 + M.cF - M.cR) i
      rw [s0, t0, s1, t1]
      simp only [Params.γ0bar, Params.γ1bar]
      set d0 := M.prodSeq (diag 1) (1 + M.cF - M.cR) i 0 - M.prodSeq (diag 0) (0 + M.cF - M.cR) i 0 with hd0
      set d1 := M.prodSeq (diag 1) (1 + M.cF - M.cR) i 1 - M.prodSeq (diag 0) (0 + M.cF - M.cR) i 1 with hd1
      have e0 : M.β * ((1 - M.γ0) * M.prodSeq (diag 1) (1 + M.cF - M.cR) i 0 + M.γ0 * M.prodSeq (diag 1) (1 + M.cF - M.cR) i 1) -
          M.β * ((1 - M.γ0) * M.prodSeq (diag 0) (0 + M.cF - M.cR) i 0 + M.γ0 * M.prodSeq (diag 0) (0 + M.cF - M.cR) i 1)
          = M.β * ((1 - M.γ0) * d0 + M.γ0 * d1) := by rw [hd0, hd1]; ring
      have e1 : M.cP + M.β * M.γ1 * (1 + M.cF - M.cR) + M.β * ((1 - M.γ1) * M.prodSeq (diag 1) (1 + M.cF - M.cR) i 1) -
          (M.cP + M.β * M.γ1 * (0 + M.cF - M.cR) + M.β * ((1 - M.γ1) * M.prodSeq (diag 0) (0 + M.cF - M.cR) i 1))
          = M.β * M.γ1 + M.β * ((1 - M.γ1) * d1) := by rw [hd1]; ring
      rw [e0, e1]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · exact mul_nonneg hb0.le (by nlinarith)
      · nlinarith [mul_nonneg hb0.le (sub_nonneg.2 a2), mul_nonneg hb0.le (sub_nonneg.2 b2), mul_nonneg hb0.le hg0.le]
      · nlinarith [mul_nonneg hb0.le (mul_nonneg (sub_nonneg.2 hg1'.le) b1)]
      · nlinarith [mul_nonneg hb0.le (mul_nonneg (sub_nonneg.2 hg1'.le) (sub_nonneg.2 b2))]
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := inv m
  have : M.anchorF m 1 - M.anchorF m 0 =
      M.β * ((1 - M.γ0) * (M.prodSeq (diag 1) (1 + M.cF - M.cR) m 0 - M.prodSeq (diag 0) (0 + M.cF - M.cR) m 0)
        + M.γ0 * (M.prodSeq (diag 1) (1 + M.cF - M.cR) m 1 - M.prodSeq (diag 0) (0 + M.cF - M.cR) m 1)) := by
    unfold Params.anchorF dot Params.p0 Params.γ0bar
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [this]
  nlinarith [mul_nonneg hb0.le (sub_nonneg.2 a2), mul_nonneg hb0.le (sub_nonneg.2 b2), mul_nonneg hb0.le hg0.le,
    mul_nonneg hb0.le (mul_nonneg hg0.le (sub_nonneg.2 b2)), mul_nonneg hb0.le (mul_nonneg (sub_nonneg.2 hg0'.le) (sub_nonneg.2 a2))]

end MaintPOMDP.Frontier

open MaintPOMDP.Frontier in
theorem solution (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (m : ℕ) :
    (∀ uR : ℝ,
        uR = M.cR + M.β * dot M.p0 (M.prodSeq (diag uR) (uR + M.cF - M.cR) m) →
        uR = M.f31 m) ∧
      M.f m = M.f31 m := by
  have hhM := hM
  obtain ⟨hb0, hb1, hcP, -, -, -, hg0, hg0', hg1, hg1'⟩ := hM
  have h0 : M.ρ0bar ≠ 0 := by
    have : 0 < M.ρ0bar := by unfold Params.ρ0bar Params.ρ0 Params.γ0bar; nlinarith
    exact this.ne'
  have h1 : M.ρ1bar ≠ 0 := by
    have : 0 < M.ρ1bar := by unfold Params.ρ1bar Params.ρ1 Params.γ1bar; nlinarith
    exact this.ne'
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hslope := vvF_slope M hhM m
  have hB : 1 - (M.anchorF m 1 - M.anchorF m 0) ≠ 0 := by linarith
  have haff : ∀ x, M.anchorF m x = M.anchorF m 0 + (M.anchorF m 1 - M.anchorF m 0) * x := by
    intro x
    rw [vvF_anchor_cf M hhM hγ, vvF_anchor_cf M hhM hγ, vvF_anchor_cf M hhM hγ]
    unfold anchorCF
    ring
  have hfm : M.f m = M.f31 m := by
    have hDn : M.ρ0bar * M.ρ1bar - M.β ^ 2 * M.γ0 * M.γ1
        - (1 - M.β) / (M.γ1 - M.γ0)
          * (M.γ1 * M.ρ1bar * M.ρ0 ^ (m + 1) - M.γ0 * M.ρ0bar * M.ρ1 ^ (m + 1))
        = M.ρ0bar * M.ρ1bar * (1 - (M.anchorF m 1 - M.anchorF m 0)) := by
      rw [vvF_anchor_cf M hhM hγ, vvF_anchor_cf M hhM hγ]
      unfold anchorCF
      simp only [pow_succ]
      generalize M.ρ0 ^ m = a
      generalize M.ρ1 ^ m = b
      simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar] at h0 h1 ⊢
      field_simp
      ring
    have hN : M.ρ0bar * M.ρ1bar * M.cR
      + (M.β * M.γ0 + M.γ0 / (M.γ1 - M.γ0)
          * (M.ρ0bar * M.ρ1 ^ (m + 1) - M.ρ1bar * M.ρ0 ^ (m + 1)))
        * (M.cP + M.β * M.γ1 * (M.cF - M.cR)) = M.ρ0bar * M.ρ1bar * M.anchorF m 0 := by
      rw [vvF_anchor_cf M hhM hγ]
      unfold anchorCF
      simp only [pow_succ]
      generalize M.ρ0 ^ m = a
      generalize M.ρ1 ^ m = b
      simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar] at h0 h1 ⊢
      field_simp
      ring
    unfold Params.f31 Params.f
    rw [hN, hDn]
    rw [mul_div_mul_left _ _ (mul_ne_zero h0 h1)]
  refine ⟨?_, hfm⟩
  intro uR hu
  have hu' : uR = M.anchorF m uR := by unfold Params.anchorF; exact hu
  rw [← hfm]
  unfold Params.f
  rw [eq_div_iff hB]
  have := haff uR
  nlinarith [this, hu']
