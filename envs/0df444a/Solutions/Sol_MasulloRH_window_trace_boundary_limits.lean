-- Prove2me | solution 1 for MasulloRH.window_trace_boundary_limits
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:43:14.370305+00:00
-- url     : https://prove2.me/submissions/a7ed5525-5733-4fcd-90a5-94b3847d3a37

import Theorems.Thm_MasulloRH_trace_window_comparison
import Mathlib.Analysis.Normed.Group.Tannery

open MasulloRH MeasureTheory Filter Set Topology

noncomputable section

private abbrev Z := ZetaZerosInTraceStrip (1/2)
private def distLine (ρ : Z) : ℝ := |(ρ:ℂ).re - 1/2|
private def capped (φ : ℝ → ℂ) (b : ℝ) (r : ℕ) (ρ : Z) : ℂ :=
  if distLine ρ < b then zetaTraceTerm φ (1/2) ρ
  else if distLine ρ = b then
    ((min (analyticOrderNatAt riemannZeta (ρ:ℂ)) r : ℕ) : ℂ) * mellin φ ((ρ:ℂ)-1/2)
  else 0

private theorem capped_le (φ : ℝ → ℂ) (b : ℝ) (r : ℕ) (ρ : Z) :
    ‖capped φ b r ρ‖ ≤ ‖zetaTraceTerm φ (1/2) ρ‖ := by
  unfold capped
  split_ifs
  · exact le_rfl
  · simp only [zetaTraceTerm,norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_left _ _) (norm_nonneg _)
  · exact (norm_zero).le.trans_eq (by simp) |>.trans (norm_nonneg _)

private def windowEquiv (α : ℝ) :
    {ρ : Z // distLine ρ < α} ≃ ZetaZerosInTraceStrip α where
  toFun x := ⟨x.val.val,x.val.property.1,x.val.property.2.1,x.val.property.2.2.1,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1,x.property.2.1,x.property.2.2.1,
    abs_lt.mpr ⟨by linarith [x.property.2.1],by linarith [x.property.2.2.1]⟩⟩,x.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem window_tsum (α : ℝ) (φ : ℝ → ℂ) :
    (∑' ρ : Z, if distLine ρ < α then zetaTraceTerm φ (1/2) ρ else 0) =
      ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  let S := {ρ : Z | distLine ρ < α}
  change (∑' ρ : Z, S.indicator (zetaTraceTerm φ (1/2)) ρ) = _
  rw [←tsum_subtype]
  exact (windowEquiv α).tsum_eq (zetaTraceTerm φ α)

private theorem window_limit (α : ℝ) (b : ℕ → ℝ) (hb : ∀ n, b n < α)
    (hlim : Tendsto b atTop (𝓝 α)) (c : ℕ → ℕ)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    Tendsto (fun n => ∑' ρ : Z, capped φ (b n) (c n) ρ) atTop
      (𝓝 (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ)) := by
  rw [←window_tsum]
  apply tendsto_tsum_of_dominated_convergence ((trace_window_comparison (1/2) φ hφ).2.2.1.norm)
  · intro ρ
    by_cases h : distLine ρ < α
    · rw [if_pos h]
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually_const_lt h] with n hn
      simp [capped,hn]
    · rw [if_neg h]
      apply tendsto_const_nhds.congr
      intro n
      have h' : b n < distLine ρ := (hb n).trans_le (le_of_not_gt h)
      simp [capped,not_lt_of_gt h',ne_of_gt h']
  · exact .of_forall (fun n ρ => capped_le φ _ _ ρ)

private theorem closed_sum_eq (α : ℝ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    (∑' ρ : Z, if distLine ρ ≤ α then zetaTraceTerm φ (1/2) ρ else 0) =
      (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) +
      ∑' ρ : {z : Z // distLine z = α}, zetaTraceTerm φ (1/2) ρ.val := by
  classical
  let l := {z : Z | distLine z < α}
  let e := {z : Z | distLine z = α}
  let F := zetaTraceTerm φ (1/2)
  have hf : Summable F := (trace_window_comparison (1/2) φ hφ).2.2.1
  rw [←window_tsum]
  change _ = (∑' z : Z, l.indicator F z) + ∑' z : e, F z.val
  rw [tsum_subtype e F]
  rw [←(hf.indicator (s := l)).tsum_add (hf.indicator (s := e))]
  apply tsum_congr
  intro z
  rcases lt_trichotomy (distLine z) α with h | h | h
  · simp [Set.indicator,l,e,h,h.le,ne_of_lt h,F]
  · simp [Set.indicator,l,e,h,F]
  · simp [Set.indicator,l,e,h.not_ge,h.not_gt,h.ne',F]

private theorem window_right_limit (α : ℝ) (b : ℕ → ℝ) (hb : ∀ n, α < b n)
    (hlim : Tendsto b atTop (𝓝 α)) (c : ℕ → ℕ)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    Tendsto (fun n => ∑' ρ : Z, capped φ (b n) (c n) ρ) atTop
      (𝓝 ((∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) +
        ∑' ρ : {z : Z // distLine z = α}, zetaTraceTerm φ (1/2) ρ.val)) := by
  rw [←closed_sum_eq α φ hφ]
  apply tendsto_tsum_of_dominated_convergence ((trace_window_comparison (1/2) φ hφ).2.2.1.norm)
  · intro ρ
    by_cases h : distLine ρ ≤ α
    · rw [if_pos h]
      apply tendsto_const_nhds.congr
      intro n
      simp [capped,h.trans_lt (hb n)]
    · rw [if_neg h]
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually_lt_const (lt_of_not_ge h)] with n hn
      simp [capped,hn.not_gt,hn.ne']
  · exact .of_forall (fun n ρ => capped_le φ _ _ ρ)

theorem solution (α : ℝ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 α)) (c : ℕ → ℕ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let F := fun n : ℕ => ∑' ρ : ZetaZerosInTraceStrip (1/2),
      if |ρ.val.re-1/2| < b n then zetaTraceTerm φ (1/2) ρ
      else if |ρ.val.re-1/2| = b n then
        ((min (analyticOrderNatAt riemannZeta ρ.val) (c n) : ℕ) : ℂ) * mellin φ (ρ.val-1/2)
      else 0
    ((∀ n, b n < α) → Tendsto F atTop (𝓝 (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ))) ∧
    ((∀ n, α < b n) → Tendsto F atTop (𝓝 ((∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) +
      ∑' ρ : {z : ZetaZerosInTraceStrip (1/2) // |z.val.re-1/2| = α}, zetaTraceTerm φ (1/2) ρ.val))) := by
  exact ⟨fun h => window_limit α b h hb c φ hφ,fun h => window_right_limit α b h hb c φ hφ⟩
