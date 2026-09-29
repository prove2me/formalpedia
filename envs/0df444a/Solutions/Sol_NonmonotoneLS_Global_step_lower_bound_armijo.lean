-- Prove2me | solution 1 for NonmonotoneLS.Global.step_lower_bound_armijo
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:51:58.506566+00:00
-- url     : https://prove2.me/submissions/e4bb037b-f07a-4033-a82a-72a0f12fced7

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter


namespace NonmonotoneLS.Global

lemma nls_Q_ge_one (η : ℕ → ℝ) (hη : ∀ k, 0 ≤ η k) : ∀ k, 1 ≤ Shared.costQ η k
  | 0 => by simp [Shared.costQ]
  | k+1 => by
    have := nls_Q_ge_one η hη k
    simp only [Shared.costQ]; nlinarith [hη k]

lemma nls_Q_le (η : ℕ → ℝ) (ηmax : ℝ) (hη : ∀ k, 0 ≤ η k ∧ η k ≤ ηmax) (h1 : ηmax ≤ 1) :
    ∀ k, (1 - ηmax) * Shared.costQ η k ≤ 1
  | 0 => by simp [Shared.costQ]; linarith [(hη 0).1, (hη 0).2]
  | k+1 => by
    have := nls_Q_le η ηmax hη h1 k
    have hQ := nls_Q_ge_one η (fun k => (hη k).1) k
    simp only [Shared.costQ]
    nlinarith [(hη k).1, (hη k).2]

lemma nls_C_succ {E : Type*} (f : E → ℝ) (x : ℕ → E) (η : ℕ → ℝ) (hη : ∀ k, 0 ≤ η k) (k : ℕ) :
    Shared.costC f x η (k+1) * Shared.costQ η (k+1) =
      η k * Shared.costQ η k * Shared.costC f x η k + f (x (k+1)) := by
  have := nls_Q_ge_one η hη (k+1)
  simp only [Shared.costC]
  rw [div_mul_cancel₀]; linarith

variable {n : ℕ}

lemma nls_step_facts (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η) (k : ℕ) :
    0 < α k ∧ f (x (k+1)) ≤ Shared.costC f x η k + p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ := by
  have h := hrun.step k
  rw [hrun.update k]
  cases r with
  | wolfe => exact ⟨h.1, h.2.1⟩
  | armijo =>
    obtain ⟨ab, hab, hh, he, hg⟩ := h
    have hρ : 0 < p.ρ := by linarith [p.one_lt_ρ]
    refine ⟨?_, ?_⟩
    · rw [he]; exact mul_pos hab (zpow_pos hρ _)
    · have := hg.1.1; rw [he]; exact this

lemma nls_cost_basic (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    ∀ k, f (x k) ≤ Shared.costC f x η k ∧ f (x (k + 1)) ≤ Shared.costC f x η k ∧
      Shared.costC f x η (k + 1) ≤ Shared.costC f x η k := by
  have hη : ∀ k, 0 ≤ η k := fun k => le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  have hnext : ∀ k, f (x (k + 1)) ≤ Shared.costC f x η k := by
    intro k
    obtain ⟨ha, hs⟩ := nls_step_facts p r f x d α η hrun k
    have : p.δ * α k * ⟪gradient f (x k), d k⟫_ℝ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg p.δ_pos.le ha.le) (hdesc k)
    linarith
  have hsucc : ∀ k, f (x (k+1)) ≤ Shared.costC f x η (k+1) ∧
      Shared.costC f x η (k + 1) ≤ Shared.costC f x η k := by
    intro k
    have hC := nls_C_succ f x η hη k
    have hQ := nls_Q_ge_one η hη k
    have hQ1 : Shared.costQ η (k+1) = η k * Shared.costQ η k + 1 := rfl
    have h1 := hnext k
    have hηQ : 0 ≤ η k * Shared.costQ η k := mul_nonneg (hη k) (by linarith)
    rw [hQ1] at hC
    constructor <;> nlinarith
  intro k
  refine ⟨?_, hnext k, (hsucc k).2⟩
  cases k with
  | zero => simp [Shared.costC]
  | succ k => exact (hsucc k).1

lemma nls_hasDerivAt_line (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (x d : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) ⟪gradient f (x + s • d), d⟫_ℝ s := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have h2 := (hf (x + s • d)).hasFDerivAt.comp_hasDerivAt s h1
  have : ⟪gradient f (x + s • d), d⟫_ℝ = fderiv ℝ f (x + s • d) d := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [this]; exact h2

lemma nls_taylor (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (x d : EuclideanSpace ℝ (Fin n)) (L μ : ℝ)
    (H : ∀ s, 0 ≤ s → s ≤ μ → ‖gradient f (x + s • d) - gradient f x‖ ≤ L * s * ‖d‖)
    (t : ℝ) (ht0 : 0 ≤ t) (htμ : t ≤ μ) :
    f (x + t • d) ≤ f x + t * ⟪gradient f x, d⟫_ℝ + L * t ^ 2 * ‖d‖ ^ 2 / 2 := by
  let ψ : ℝ → ℝ := fun s => f (x + s • d) - s * ⟪gradient f x, d⟫_ℝ - L * s ^ 2 * ‖d‖ ^ 2 / 2
  have hd : ∀ s, HasDerivAt ψ (⟪gradient f (x + s • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ
      - L * s * ‖d‖ ^ 2) s := by
    intro s
    have := ((nls_hasDerivAt_line f hf x d s).sub ((hasDerivAt_id s).mul_const
      ⟪gradient f x, d⟫_ℝ)).sub (((hasDerivAt_pow 2 s).const_mul L).mul_const (‖d‖ ^ 2 / 2))
    have hfun : (((fun t => f (x + t • d)) - fun y => id y * ⟪gradient f x, d⟫_ℝ) -
        fun y => L * y ^ 2 * (‖d‖ ^ 2 / 2)) = ψ := by
      ext s; simp only [ψ, id, Pi.sub_apply]; ring
    rw [hfun] at this
    refine this.congr_deriv ?_
    have : ((2:ℕ):ℝ) * s ^ (2 - 1) = 2 * s := by norm_num
    rw [this]; ring
  have hanti : AntitoneOn ψ (Set.Icc 0 t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      have h1 := H s hs.1.le (by linarith [hs.2])
      have h2 : ⟪gradient f (x + s • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ ≤
          ‖gradient f (x + s • d) - gradient f x‖ * ‖d‖ := by
        rw [← inner_sub_left]; exact real_inner_le_norm _ _
      have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg d)
      nlinarith
  have := hanti (Set.left_mem_Icc.2 ht0) (Set.right_mem_Icc.2 ht0) ht0
  simp only [ψ, zero_smul, add_zero, zero_mul, sub_zero] at this
  nlinarith


lemma nls_Q_le_succ (η : ℕ → ℝ) (hη : ∀ k, 0 ≤ η k ∧ η k ≤ 1) :
    ∀ k : ℕ, Shared.costQ η k ≤ (k : ℝ) + 1
  | 0 => by simp [Shared.costQ]
  | k+1 => by
    have := nls_Q_le_succ η hη k
    have hQ := nls_Q_ge_one η (fun k => (hη k).1) k
    simp only [Shared.costQ]; push_cast
    nlinarith [(hη k).1, (hη k).2]

theorem cost_bounds_core {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    ∀ k, f (x k) ≤ Shared.costC f x η k ∧ Shared.costC f x η k ≤ Shared.avgA f x k := by
  have hb := nls_cost_basic p r f x d α η hrun hdesc
  have hη : ∀ k, 0 ≤ η k := fun k => le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  have hη1 : ∀ k, 0 ≤ η k ∧ η k ≤ 1 :=
    fun k => ⟨hη k, le_trans (hrun.eta_mem k).2 p.ηmax_le_one⟩
  intro k
  refine ⟨(hb k).1, ?_⟩
  induction k with
  | zero => simp [Shared.costC, Shared.avgA]
  | succ k ih =>
    have hC := nls_C_succ f x η hη k
    have hQk := nls_Q_ge_one η hη k
    have hQle := nls_Q_le_succ η hη1 k
    have hQ1 : Shared.costQ η (k+1) = η k * Shared.costQ η k + 1 := rfl
    have hA : Shared.avgA f x (k+1) * ((k:ℝ) + 2) =
        ((k:ℝ) + 1) * Shared.avgA f x k + f (x (k+1)) := by
      simp only [Shared.avgA]
      rw [Finset.sum_range_succ]
      field_simp
      push_cast; ring
    set s := η k * Shared.costQ η k with hs
    have hs0 : 0 ≤ s := mul_nonneg (hη k) (by linarith)
    have hs1 : s ≤ (k:ℝ) + 1 := by
      have := mul_le_mul (hη1 k).2 hQle (by linarith) zero_le_one
      linarith
    have hf1 := (hb k).2.1
    rw [hQ1] at hC
    set C := Shared.costC f x η k
    set C' := Shared.costC f x η (k+1)
    set A := Shared.avgA f x k
    set A' := Shared.avgA f x (k+1)
    set F := f (x (k+1))
    -- C' (s+1) = s C + F
    have key : C' * ((k:ℝ) + 2) ≤ ((k:ℝ) + 1) * C + F := by
      have h1 : (C' * ((k:ℝ) + 2)) * (s + 1) ≤ (((k:ℝ) + 1) * C + F) * (s + 1) := by
        have : (C' * ((k:ℝ) + 2)) * (s + 1) = (s * C + F) * ((k:ℝ) + 2) := by
          rw [← hC]; ring
        rw [this]; nlinarith [mul_nonneg (sub_nonneg.2 hf1) (sub_nonneg.2 hs1)]
      exact le_of_mul_le_mul_right h1 (by linarith)
    have : C' * ((k:ℝ) + 2) ≤ A' * ((k:ℝ) + 2) := by
      rw [hA]; nlinarith
    exact le_of_mul_le_mul_right this (by positivity)

theorem wolfe_lb_core {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0)
    (hstep : Shared.IsWolfeStep p f x d C α)
    (hLip : ‖gradient f (x + α • d) - gradient f x‖ ≤ L * ‖(x + α • d) - x‖) :
    (1 - p.σ) / L * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2) ≤ α := by
  obtain ⟨hα, -, hcurv⟩ := hstep
  rcases eq_or_lt_of_le (norm_nonneg d) with hd0 | hdpos
  · rw [← hd0]; simp; exact hα.le
  have e : x + α • d - x = α • d := by abel
  rw [e, norm_smul, Real.norm_of_nonneg hα.le] at hLip
  have hin : ⟪gradient f (x + α • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ ≤
      ‖gradient f (x + α • d) - gradient f x‖ * ‖d‖ := by
    rw [← inner_sub_left]; exact real_inner_le_norm _ _
  have h3 := mul_le_mul_of_nonneg_right hLip (norm_nonneg d)
  rw [abs_of_nonpos hdesc]
  have hσ := p.σ_lt_one
  have key : (1 - p.σ) * (-⟪gradient f x, d⟫_ℝ) ≤ α * (L * ‖d‖ ^ 2) := by nlinarith
  rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
  linarith

lemma nls_seg_mem {n : ℕ} (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 < t) (s : ℝ)
    (hs0 : 0 ≤ s) (hst : s ≤ t) : x + s • d ∈ segment ℝ x (x + t • d) := by
  rw [segment_eq_image']
  refine ⟨s / t, ⟨div_nonneg hs0 ht.le, (div_le_one ht).2 hst⟩, ?_⟩
  simp only [add_sub_cancel_left, smul_smul]
  rw [div_mul_cancel₀ _ ht.ne']

theorem armijo_lb_core {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0) (hfC : f x ≤ C)
    (hstep : Shared.IsArmijoStep p f x d C α)
    (hLip : p.ρ * α ≤ p.μ → ∀ y ∈ segment ℝ x (x + (p.ρ * α) • d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖) :
    min (p.μ / p.ρ)
        (2 * (1 - p.δ) / (L * p.ρ) * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2)) ≤ α := by
  obtain ⟨ab, hab, h, he, hgr⟩ := hstep
  have hρ0 : (0:ℝ) < p.ρ := by linarith [p.one_lt_ρ]
  have hα : 0 < α := by rw [he]; exact mul_pos hab (zpow_pos hρ0 _)
  have hnot : (h + 1) ∉ Shared.armijoAdmissible p f x d C ab := by
    intro hm; have := hgr.2 hm; omega
  have hpow : ab * p.ρ ^ (h + 1) = α * p.ρ := by
    rw [he, zpow_add_one₀ hρ0.ne']; ring
  simp only [Shared.armijoAdmissible, Set.mem_setOf_eq, hpow, not_and_or, not_le] at hnot
  have hbig : p.μ < α * p.ρ → min (p.μ / p.ρ)
      (2 * (1 - p.δ) / (L * p.ρ) * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2)) ≤ α := by
    intro hb
    refine le_trans (min_le_left _ _) ?_
    rw [div_le_iff₀ hρ0]; linarith
  rcases le_or_gt (α * p.ρ) p.μ with hle | hb
  · rcases hnot with hfail | hb
    · set t := α * p.ρ with ht
      have ht0 : 0 < t := by positivity
      have H : ∀ s, 0 ≤ s → s ≤ t → ‖gradient f (x + s • d) - gradient f x‖ ≤ L * s * ‖d‖ := by
        intro s hs0 hst
        have := hLip (by rw [mul_comm]; exact hle) (x + s • d)
          (by rw [mul_comm]; exact nls_seg_mem x d t ht0 s hs0 hst)
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0] at this
        linarith
      have hT := nls_taylor f (hf.differentiable one_ne_zero) x d L t H t ht0.le le_rfl
      have hδ1 : p.δ < 1 := by linarith [p.δ_lt_σ, p.σ_lt_one]
      have h8 : (1 - p.δ) * t * (-⟪gradient f x, d⟫_ℝ) < L * t ^ 2 * ‖d‖ ^ 2 / 2 := by
        nlinarith
      have h9 : 2 * (1 - p.δ) * (-⟪gradient f x, d⟫_ℝ) < L * t * ‖d‖ ^ 2 := by
        have h10 : (2 * (1 - p.δ) * (-⟪gradient f x, d⟫_ℝ)) * t < (L * t * ‖d‖ ^ 2) * t := by
          nlinarith
        exact lt_of_mul_lt_mul_right h10 ht0.le
      rcases eq_or_lt_of_le (norm_nonneg d) with hd0 | hdpos
      · rw [← hd0] at h9; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * (1 - p.δ)) (neg_nonneg.2 hdesc)]
      refine le_trans (min_le_right _ _) ?_
      rw [abs_of_nonpos hdesc, div_mul_div_comm, div_le_iff₀ (by positivity)]
      rw [ht] at h9; nlinarith
    · exact hbig hb
  · exact hbig hb

end NonmonotoneLS.Global

open NonmonotoneLS.Global
open NonmonotoneLS

theorem solution {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (C α L : ℝ) (hL : 0 < L)
    (hdesc : ⟪gradient f x, d⟫_ℝ ≤ 0) (hfC : f x ≤ C)
    (hstep : Shared.IsArmijoStep p f x d C α)
    (hLip : p.ρ * α ≤ p.μ → ∀ y ∈ segment ℝ x (x + (p.ρ * α) • d),
      ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖) :
    min (p.μ / p.ρ)
        (2 * (1 - p.δ) / (L * p.ρ) * (|⟪gradient f x, d⟫_ℝ| / ‖d‖ ^ 2)) ≤ α := by
  exact armijo_lb_core p f hf x d C α L hL hdesc hfC hstep hLip
