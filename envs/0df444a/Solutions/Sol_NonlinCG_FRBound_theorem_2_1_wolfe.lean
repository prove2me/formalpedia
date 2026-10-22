-- Prove2me | solution 1 for NonlinCG.FRBound.theorem_2_1_wolfe
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:38:55.645143+00:00
-- url     : https://prove2.me/submissions/d9db121b-d8fa-405b-b119-70c9c6da9673

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting



namespace NonlinCG.FRBound

theorem zout_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (α : ℕ → ℝ) (x d : ℕ → E)
    (σ₁ σ₂ : ℝ) (hA : Assumptions21 f (x 1))
    (hσ : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1)
    (hiter : ∀ k ≥ 1, 0 < α k ∧ x (k + 1) = x k + α k • d k)
    (hdesc : ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0)
    (hls : ∀ k ≥ 1, WolfeStep f σ₁ σ₂ (x k) (d k) (α k)) :
    ZoutendijkCondition f x d := by
  obtain ⟨hbd, N, hNo, hLN, -, L, hL, hLip⟩ := hA
  obtain ⟨hσ1, hσ12, hσ2⟩ := hσ
  -- decrease
  have hdec : ∀ k ≥ 1, f (x (k+1)) ≤ f (x k) := by
    intro k hk
    have h1 := (hls k hk).1
    have h2 := hdesc k hk
    have h3 := (hiter k hk).1
    rw [(hiter k hk).2]
    have : σ₁ * α k * inner ℝ (gradient f (x k)) (d k) ≤ 0 := by
      have : inner ℝ (gradient f (x k)) (d k) < 0 := h2
      have := mul_pos hσ1 h3
      nlinarith
    linarith
  have hle : ∀ k ≥ 1, f (x k) ≤ f (x 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hdec n hn).trans ih
  have hcl : IsClosed (levelSet f (x 1)) := isClosed_le hf.continuous continuous_const
  have hcp : IsCompact (levelSet f (x 1)) := Metric.isCompact_of_isClosed_isBounded hcl hbd
  have hbb : BddBelow (f '' levelSet f (x 1)) := (hcp.image hf.continuous).bddBelow
  obtain ⟨m, hm⟩ := hbb
  have hmk : ∀ k ≥ 1, m ≤ f (x k) := fun k hk => hm ⟨x k, hle k hk, rfl⟩
  have hLpos : (0:ℝ) < L := by exact_mod_cast hL
  set c : ℝ := σ₁ * (1 - σ₂) / L with hc
  have hcpos : 0 < c := by
    rw [hc]; apply div_pos (mul_pos hσ1 (by linarith)) hLpos
  have key : ∀ k ≥ 1, f (x (k+1)) ≤ f (x k) - c * (inner ℝ (g f x k) (d k) ^ 2 / ‖d k‖ ^ 2) := by
    intro k hk
    have ha := hdesc k hk
    set a := inner ℝ (g f x k) (d k) with hadef
    have hd0 : d k ≠ 0 := by
      intro h; rw [h, inner_zero_right] at hadef; rw [hadef] at ha; exact lt_irrefl _ ha
    have hD : 0 < ‖d k‖ ^ 2 := by positivity
    obtain ⟨hα, hx⟩ := hiter k hk
    obtain ⟨w1, w2⟩ := hls k hk
    have hxk : x k ∈ levelSet f (x 1) := hle k hk
    have hxk1 : x (k+1) ∈ levelSet f (x 1) := hle (k+1) (by omega)
    have hlip := hLip.dist_le_mul (x (k+1)) (hNo.mem_nhds_iff.mpr (hLN hxk1) |> fun _ => hLN hxk1) (x k) (hLN hxk)
    have hn : ‖gradient f (x k + α k • d k) - gradient f (x k)‖ ≤ L * (α k * ‖d k‖) := by
      have := hlip
      rw [dist_eq_norm, dist_eq_norm, hx] at this
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hα] at this
      exact this
    have hin : inner ℝ (gradient f (x k + α k • d k) - gradient f (x k)) (d k) ≤ L * α k * ‖d k‖ ^ 2 := by
      calc _ ≤ ‖gradient f (x k + α k • d k) - gradient f (x k)‖ * ‖d k‖ := real_inner_le_norm _ _
        _ ≤ L * (α k * ‖d k‖) * ‖d k‖ := by gcongr
        _ = _ := by ring
    rw [inner_sub_left] at hin
    have hgk : inner ℝ (g f x k) (d k) = inner ℝ (gradient f (x k)) (d k) := rfl
    have hw2 : σ₂ * inner ℝ (gradient f (x k)) (d k) ≤ inner ℝ (gradient f (x k + α k • d k)) (d k) := w2
    have hLa : (1 - σ₂) * (-a) ≤ L * α k * ‖d k‖ ^ 2 := by
      have e : a = inner ℝ (gradient f (x k)) (d k) := rfl
      rw [← e] at hin hw2
      nlinarith
    have hfx : f (x (k+1)) ≤ f (x k) + σ₁ * α k * a := by rw [hx]; exact w1
    have : c * (a ^ 2 / ‖d k‖ ^ 2) ≤ -(σ₁ * α k * a) := by
      rw [hc]
      have e : σ₁ * (1 - σ₂) / L * (a ^ 2 / ‖d k‖ ^ 2) = σ₁ * (-a) * ((1 - σ₂) * (-a)) / (L * ‖d k‖ ^ 2) := by
        field_simp
      rw [e, div_le_iff₀ (by positivity)]
      have h1 : 0 ≤ σ₁ * (-a) := by nlinarith
      calc σ₁ * (-a) * ((1 - σ₂) * (-a)) ≤ σ₁ * (-a) * (L * α k * ‖d k‖ ^ 2) := by gcongr
        _ = _ := by ring
    linarith
  -- summability
  unfold ZoutendijkCondition
  have hnn : ∀ k : ℕ, 0 ≤ inner ℝ (g f x (k + 1)) (d (k + 1)) ^ 2 / ‖d (k + 1)‖ ^ 2 := fun k => by positivity
  apply summable_of_sum_range_le hnn (c := (f (x 1) - m) / c)
  intro n
  have hs : c * ∑ i ∈ Finset.range n, inner ℝ (g f x (i + 1)) (d (i + 1)) ^ 2 / ‖d (i + 1)‖ ^ 2 ≤ f (x 1) - m := by
    have : ∀ n : ℕ, c * ∑ i ∈ Finset.range n, inner ℝ (g f x (i + 1)) (d (i + 1)) ^ 2 / ‖d (i + 1)‖ ^ 2 ≤ f (x 1) - f (x (n+1)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := key (n+1) (by omega)
        linarith
    have h2 := this n
    have := hmk (n+1) (by omega)
    linarith
  rw [le_div_iff₀ hcpos]; linarith

end NonlinCG.FRBound

open NonlinCG.FRBound


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (α : ℕ → ℝ) (x d : ℕ → E)
    (σ₁ σ₂ : ℝ) (hA : Assumptions21 f (x 1))
    (hσ : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1)
    (hiter : ∀ k ≥ 1, 0 < α k ∧ x (k + 1) = x k + α k • d k)
    (hdesc : ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0)
    (hls : ∀ k ≥ 1, WolfeStep f σ₁ σ₂ (x k) (d k) (α k)) :
    ZoutendijkCondition f x d := by
  exact zout_core f hf α x d σ₁ σ₂ hA hσ (fun k hk => hiter k hk) hdesc hls
