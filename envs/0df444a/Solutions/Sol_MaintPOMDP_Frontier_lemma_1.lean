-- Prove2me | solution 1 for MaintPOMDP.Frontier.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:13.880099+00:00
-- url     : https://prove2.me/submissions/fd6bd434-0725-4a3e-b0a1-e352a191be8a

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

end MaintPOMDP.Frontier

open MaintPOMDP.Frontier in
theorem solution (M : Params) (hM : M.Standing) (hγ : M.γ0 ≠ M.γ1) (uR uF : ℝ) (huF : 0 < uF)
    (i : ℕ) : M.prodSeq (diag uR) uF i = M.seq29_30 uR uF i := by
  have h := (qqE_prod_closed M hM hγ (diag uR) uF i)
  have hd : M.γ1 - M.γ0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  have hg1 : M.γ1 ≠ 0 := hM.2.2.2.2.2.2.2.2.1.ne'
  have h0 : M.ρ0bar ≠ 0 := by
    obtain ⟨hb0, hb1, -, -, -, -, hg0, hg0', hg1, hg1'⟩ := hM
    have : 0 < M.ρ0bar := by unfold Params.ρ0bar Params.ρ0 Params.γ0bar; nlinarith
    exact this.ne'
  have h1 : M.ρ1bar ≠ 0 := by
    obtain ⟨hb0, hb1, -, -, -, -, hg0, hg0', hg1, hg1'⟩ := hM
    have : 0 < M.ρ1bar := by unfold Params.ρ1bar Params.ρ1 Params.γ1bar; nlinarith
    exact this.ne'
  obtain ⟨c1, c0⟩ := h
  simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar] at h0 h1 c0 c1
  funext j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [c0]
    simp only [diag, Matrix.cons_val_zero, Matrix.cons_val_one, Params.seq29_30]
    simp only [Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar]
    field_simp
    ring
  · simp only [Fin.mk_one, Fin.isValue]
    rw [c1]
    simp [diag, Params.seq29_30, Params.ρ0bar, Params.ρ1bar, Params.ρ0, Params.ρ1, Params.γ0bar, Params.γ1bar]
