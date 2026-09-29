-- Prove2me | solution 1 for NonmonotoneLS.RLinear.cost_contraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:59:07.885367+00:00
-- url     : https://prove2.me/submissions/3b5d1355-294b-49f9-95e9-a570418a64bc

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter


namespace NonmonotoneLS.RLinear

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


lemma nls_sd_core (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ) (L : ℝ) (hL : 0 < L)
    (HL : ∀ k s, 0 ≤ s → s ≤ p.μ →
      ‖gradient f (x k + s • d k) - gradient f (x k)‖ ≤ L * s * ‖d k‖) :
    ∀ k, f (x (k + 1)) ≤ Shared.costC f x η k - beta p c₁ c₂ L * ‖gradient f (x k)‖ ^ 2 := by
  have hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0 := by
    intro k; have := (hdir k).1; nlinarith [sq_nonneg ‖gradient f (x k)‖]
  have hbasic := nls_cost_basic p r f x d α η hrun hdesc
  intro k
  obtain ⟨hα, hs⟩ := nls_step_facts p r f x d α η hrun k
  obtain ⟨h1, h2⟩ := hdir k
  set g := gradient f (x k) with hg
  have hδ := p.δ_pos
  have hσ1 := p.σ_lt_one
  have hδσ := p.δ_lt_σ
  have hρ := p.one_lt_ρ
  have hμ := p.μ_pos
  rcases eq_or_lt_of_le (norm_nonneg g) with hg0 | hgpos
  · rw [← hg0]
    have : p.δ * α k * ⟪g, d k⟫_ℝ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hδ.le hα.le) (hdesc k)
    simp; linarith
  -- key: beta ≤ δ α c₁
  suffices key : beta p c₁ c₂ L ≤ p.δ * α k * c₁ by
    have e1 : p.δ * α k * ⟪g, d k⟫_ℝ ≤ p.δ * α k * (-c₁ * ‖g‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hδ.le hα.le)
    have e2 := mul_le_mul_of_nonneg_right key (sq_nonneg ‖g‖)
    nlinarith
  have hG2 : 0 < ‖g‖ ^ 2 := by positivity
  have hdd : ‖d k‖ ^ 2 ≤ c₂ ^ 2 * ‖g‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hgd : c₁ * ‖g‖ ^ 2 ≤ -⟪g, d k⟫_ℝ := by linarith
  cases hr : r with
  | wolfe =>
    have hst := hrun.step k
    rw [hr] at hst
    obtain ⟨-, -, hcurv⟩ := hst
    rw [← hrun.update k] at hcurv
    have hL1 := HL k (α k) hα.le (hαμ k)
    rw [← hrun.update k] at hL1
    have hin : ⟪gradient f (x (k+1)), d k⟫_ℝ - ⟪g, d k⟫_ℝ ≤
        ‖gradient f (x (k+1)) - g‖ * ‖d k‖ := by
      rw [← inner_sub_left]; exact real_inner_le_norm _ _
    have h3 := mul_le_mul_of_nonneg_right hL1 (norm_nonneg (d k))
    -- (1-σ) c₁ ‖g‖² ≤ L α c₂² ‖g‖²
    have h4 : (1 - p.σ) * c₁ * ‖g‖ ^ 2 ≤ L * α k * c₂ ^ 2 * ‖g‖ ^ 2 := by
      have : (1 - p.σ) * (-⟪g, d k⟫_ℝ) ≤ L * α k * ‖d k‖ ^ 2 := by nlinarith
      have h5 : (1 - p.σ) * (c₁ * ‖g‖ ^ 2) ≤ (1 - p.σ) * (-⟪g, d k⟫_ℝ) :=
        mul_le_mul_of_nonneg_left hgd (by linarith)
      have h6 : L * α k * ‖d k‖ ^ 2 ≤ L * α k * (c₂ ^ 2 * ‖g‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdd (by positivity)
      nlinarith
    have h7 : (1 - p.σ) * c₁ ≤ L * α k * c₂ ^ 2 := le_of_mul_le_mul_right h4 hG2
    refine le_trans (min_le_right _ _) ?_
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left h7 (mul_nonneg hδ.le hc₁.le)
    nlinarith
  | armijo =>
    have hst := hrun.step k
    rw [hr] at hst
    obtain ⟨ab, hab, h, he, hgr⟩ := hst
    have hnot : (h + 1) ∉ Shared.armijoAdmissible p f (x k) (d k) (Shared.costC f x η k) ab := by
      intro hm; have := hgr.2 hm; omega
    have hρ0 : (0:ℝ) < p.ρ := by linarith
    have hpow : ab * p.ρ ^ (h + 1) = α k * p.ρ := by
      rw [he, zpow_add_one₀ hρ0.ne']; ring
    simp only [Shared.armijoAdmissible, Set.mem_setOf_eq, hpow, not_and_or, not_le] at hnot
    rcases hnot with hfail | hbig
    · -- α ρ ≤ μ case handled via Taylor, unless αρ > μ
      rcases le_or_gt (α k * p.ρ) p.μ with hle | hbig
      · have hT := nls_taylor f hf (x k) (d k) L p.μ (HL k) (α k * p.ρ) (by positivity) hle
        have hfC := (hbasic k).1
        -- (1-δ) t (-gd) < L t² ‖d‖²/2
        set t := α k * p.ρ with ht
        have ht0 : 0 < t := by positivity
        have h8 : (1 - p.δ) * t * (-⟪g, d k⟫_ℝ) < L * t ^ 2 * ‖d k‖ ^ 2 / 2 := by linarith
        have h9 : (1 - p.δ) * t * (c₁ * ‖g‖ ^ 2) ≤ (1 - p.δ) * t * (-⟪g, d k⟫_ℝ) :=
          mul_le_mul_of_nonneg_left hgd (by nlinarith)
        have h10 : L * t ^ 2 * ‖d k‖ ^ 2 / 2 ≤ L * t ^ 2 * (c₂ ^ 2 * ‖g‖ ^ 2) / 2 := by
          have := mul_le_mul_of_nonneg_left hdd (by positivity : 0 ≤ L * t ^ 2); linarith
        have h11 : (2 * (1 - p.δ) * c₁) * (t * ‖g‖ ^ 2) < (L * t * c₂ ^ 2) * (t * ‖g‖ ^ 2) := by
          linarith
        have h12 : 2 * (1 - p.δ) * c₁ < L * t * c₂ ^ 2 := lt_of_mul_lt_mul_right h11 (by positivity)
        refine le_trans (min_le_left _ _) (le_trans (min_le_right _ _) ?_)
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left h12.le (mul_nonneg hδ.le hc₁.le)
        rw [ht] at this
        linarith
      · refine le_trans (min_le_left _ _) (le_trans (min_le_left _ _) ?_)
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hbig.le (mul_nonneg hδ.le hc₁.le)
        linarith
    · refine le_trans (min_le_left _ _) (le_trans (min_le_left _ _) ?_)
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hbig.le (mul_nonneg hδ.le hc₁.le)
      linarith


lemma nls_beta_pos (p : Shared.Params) (c₁ c₂ L : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL : 0 < L) :
    0 < beta p c₁ c₂ L := by
  have hδ := p.δ_pos
  have h1 : 0 < 1 - p.δ := by linarith [p.δ_lt_σ, p.σ_lt_one]
  have h2 : 0 < 1 - p.σ := by linarith [p.σ_lt_one]
  have hρ : 0 < p.ρ := by linarith [p.one_lt_ρ]
  have hμ := p.μ_pos
  unfold beta
  refine lt_min (lt_min ?_ ?_) ?_ <;> positivity

lemma nls_theta_bounds (p : Shared.Params) (c₁ c₂ L γ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hL : 0 < L) (hγ : 0 < γ) (hηmax : p.ηmax < 1) :
    0 < theta p c₁ c₂ L γ ∧ theta p c₁ c₂ L γ < 1 := by
  have hβ := nls_beta_pos p c₁ c₂ L hc₁ hc₂ hL
  have hb : 0 < bConst p c₂ L := by unfold bConst; have := p.μ_pos; positivity
  have hη0 : 0 ≤ p.ηmax := le_trans p.ηmin_nonneg p.ηmin_le_ηmax
  have hden : 0 < beta p c₁ c₂ L + γ * bConst p c₂ L ^ 2 := by positivity
  have hq : beta p c₁ c₂ L * b2Const p c₁ c₂ L γ < 1 := by
    unfold b2Const; rw [mul_one_div, div_lt_one hden]
    have : 0 < γ * bConst p c₂ L ^ 2 := by positivity
    linarith
  have hq0 : 0 < beta p c₁ c₂ L * b2Const p c₁ c₂ L γ := by unfold b2Const; positivity
  unfold theta
  constructor
  · have : beta p c₁ c₂ L * b2Const p c₁ c₂ L γ * (1 - p.ηmax) ≤
        beta p c₁ c₂ L * b2Const p c₁ c₂ L γ := by nlinarith
    linarith
  · have : 0 < beta p c₁ c₂ L * b2Const p c₁ c₂ L γ * (1 - p.ηmax) := by
      apply mul_pos hq0; linarith
    linarith

lemma nls_subopt (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) :
    ∀ y, f y - f xstar ≤ γ * ‖gradient f y‖ ^ 2 := by
  intro y
  obtain ⟨hγ, h⟩ := hsc
  have h1 := h xstar y
  have h2 : -(‖gradient f y‖ * ‖xstar - y‖) ≤ ⟪gradient f y, xstar - y⟫_ℝ := by
    have := abs_real_inner_le_norm (gradient f y) (xstar - y)
    rw [abs_le] at this; linarith [this.1]
  have h3 : ‖gradient f y‖ * ‖xstar - y‖ - γ * ‖gradient f y‖ ^ 2 / 2 ≤
      1 / (2 * γ) * ‖xstar - y‖ ^ 2 := by
    rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (γ * ‖gradient f y‖ - ‖xstar - y‖)]
  nlinarith [sq_nonneg ‖gradient f y‖]

lemma nls_grad_growth_core (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ) (L : ℝ) (hL : 0 ≤ L)
    (HL : ∀ k s, 0 ≤ s → s ≤ p.μ →
      ‖gradient f (x k + s • d k) - gradient f (x k)‖ ≤ L * s * ‖d k‖) :
    ∀ k, ‖gradient f (x (k + 1))‖ ≤ bConst p c₂ L * ‖gradient f (x k)‖ := by
  intro k
  obtain ⟨hα, -⟩ := nls_step_facts p r f x d α η hrun k
  have h1 := HL k (α k) hα.le (hαμ k)
  rw [← hrun.update k] at h1
  have h2 : ‖gradient f (x (k + 1))‖ ≤ ‖gradient f (x (k + 1)) - gradient f (x k)‖ +
      ‖gradient f (x k)‖ := norm_le_norm_sub_add _ _
  have h3 : L * α k * ‖d k‖ ≤ L * p.μ * (c₂ * ‖gradient f (x k)‖) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left (hαμ k) hL) (hdir k).2 (norm_nonneg _)
    exact mul_nonneg hL p.μ_pos.le
  unfold bConst
  nlinarith

lemma nls_contract_core (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ) (L : ℝ) (hL : 0 < L)
    (HL : ∀ k s, 0 ≤ s → s ≤ p.μ →
      ‖gradient f (x k + s • d k) - gradient f (x k)‖ ≤ L * s * ‖d k‖) :
    ∀ k, Shared.costC f x η (k + 1) - f xstar ≤
      theta p c₁ c₂ L γ * (Shared.costC f x η k - f xstar) := by
  have hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0 := by
    intro k; have := (hdir k).1; nlinarith [sq_nonneg ‖gradient f (x k)‖]
  have hbasic := nls_cost_basic p r f x d α η hrun hdesc
  have hsd := nls_sd_core p r f hf x d α η hrun c₁ c₂ hc₁ hc₂ hdir hαμ L hL HL
  have hgr := nls_grad_growth_core p r f x d α η hrun c₁ c₂ hc₂ hdir hαμ L hL.le HL
  have hη : ∀ k, 0 ≤ η k := fun k => le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  have hηle : ∀ k, 0 ≤ η k ∧ η k ≤ p.ηmax := fun k => ⟨hη k, (hrun.eta_mem k).2⟩
  intro k
  have hγ := hsc.1
  have hβ := nls_beta_pos p c₁ c₂ L hc₁ hc₂ hL
  have hb : 0 < bConst p c₂ L := by unfold bConst; have := p.μ_pos; positivity
  set β := beta p c₁ c₂ L with hβdef
  set b := bConst p c₂ L with hbdef
  have hB2 : b2Const p c₁ c₂ L γ = 1 / (β + γ * b ^ 2) := rfl
  set B2 := b2Const p c₁ c₂ L γ with hB2def
  have hden : 0 < β + γ * b ^ 2 := by positivity
  have hB2pos : 0 < B2 := by rw [hB2]; positivity
  have hsum : β * B2 + γ * b ^ 2 * B2 = 1 := by
    rw [hB2]; field_simp
  have hθ : theta p c₁ c₂ L γ = 1 - β * B2 * (1 - p.ηmax) := rfl
  rw [hθ]
  set e := Shared.costC f x η k - f xstar with he
  set G := ‖gradient f (x k)‖ ^ 2 with hG
  have he0 : 0 ≤ e := by have := (hbasic k).1; have := hmin (x k); linarith
  have hG0 : 0 ≤ G := by positivity
  have hs1 := hsd k
  have hsub := nls_subopt f γ hsc xstar (x (k+1))
  have hg2 : ‖gradient f (x (k + 1))‖ ^ 2 ≤ b ^ 2 * G := by
    rw [hG, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hgr k) 2
  have hfn : f (x (k+1)) - f xstar ≤ (1 - β * B2) * e := by
    rcases le_or_gt (B2 * e) G with hc | hc
    · have := mul_le_mul_of_nonneg_left hc hβ.le
      nlinarith
    · have h1 : γ * ‖gradient f (x (k + 1))‖ ^ 2 ≤ γ * (b ^ 2 * G) :=
        mul_le_mul_of_nonneg_left hg2 hγ.le
      have h2 : γ * b ^ 2 * G ≤ γ * b ^ 2 * (B2 * e) :=
        mul_le_mul_of_nonneg_left hc.le (by positivity)
      have h3 : (1 - β * B2) * e = γ * b ^ 2 * (B2 * e) := by
        have : 1 - β * B2 = γ * b ^ 2 * B2 := by linarith
        rw [this]; ring
      nlinarith
  have hC := nls_C_succ f x η hη k
  have hQ := nls_Q_ge_one η hη k
  have hQ' := nls_Q_ge_one η hη (k+1)
  have hQle := nls_Q_le η p.ηmax hηle p.ηmax_le_one (k+1)
  have hQ1 : Shared.costQ η (k+1) = η k * Shared.costQ η k + 1 := rfl
  set Q' := Shared.costQ η (k+1)
  have hQ'pos : 0 < Q' := by linarith
  -- (C' - f*) Q' ≤ Q' e - β B2 e
  have hmain : (Shared.costC f x η (k + 1) - f xstar) * Q' ≤ Q' * e - β * B2 * e := by
    have : (Shared.costC f x η (k + 1) - f xstar) * Q' =
        η k * Shared.costQ η k * e + (f (x (k+1)) - f xstar) := by
      rw [sub_mul, hC, he, hQ1]; ring
    rw [this]; rw [hQ1] at ⊢; nlinarith
  have hbe : 0 ≤ β * B2 * e := by positivity
  have hfin : Q' * e - β * B2 * e ≤ (1 - β * B2 * (1 - p.ηmax)) * e * Q' := by
    have := mul_le_mul_of_nonneg_left hQle hbe
    nlinarith
  exact le_of_mul_le_mul_right (by nlinarith) hQ'pos


lemma nls_level (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) : ∀ k, f (x k) ≤ f (x 0) := by
  have hb := nls_cost_basic p r f x d α η hrun hdesc
  have hanti : Antitone (Shared.costC f x η) := antitone_nat_of_succ_le (fun k => (hb k).2.2)
  intro k
  have := hanti (Nat.zero_le k)
  have h0 : Shared.costC f x η 0 = f (x 0) := rfl
  linarith [(hb k).1]

lemma nls_HL_of_Lbar (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k s, 0 ≤ s → s ≤ p.μ →
      ‖gradient f (x k + s • d k) - gradient f (x k)‖ ≤ (L : ℝ) * s * ‖d k‖ := by
  have hlev := nls_level p r f x d α η hrun hdesc
  have mem : ∀ k s, 0 ≤ s → s ≤ p.μ → x k + s • d k ∈ Lbar p f x d := by
    intro k s hs0 hsμ
    show Metric.infEDist _ _ ≤ _
    have hxk : x k ∈ levelSet f (x 0) := hlev k
    calc Metric.infEDist (x k + s • d k) (levelSet f (x 0))
        ≤ edist (x k + s • d k) (x k) := Metric.infEDist_le_edist_of_mem hxk
      _ = ENNReal.ofReal (s * ‖d k‖) := by
          rw [edist_dist, dist_eq_norm]; simp [norm_smul, abs_of_nonneg hs0]
      _ ≤ ENNReal.ofReal (p.μ * ‖d k‖) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hsμ (norm_nonneg _))
      _ = ENNReal.ofReal p.μ * (‖d k‖₊ : ENNReal) := by
          rw [ENNReal.ofReal_mul p.μ_pos.le]; congr 1
          exact ofReal_norm_eq_enorm _
      _ ≤ ENNReal.ofReal p.μ * dmax d := by
          gcongr; exact le_iSup (fun k => (‖d k‖₊ : ENNReal)) k
  intro k s hs0 hsμ
  have h1 := mem k s hs0 hsμ
  have h2 := mem k 0 le_rfl p.μ_pos.le
  simp only [zero_smul, add_zero] at h2
  have := hLip.dist_le_mul _ h1 _ h2
  rw [dist_eq_norm, dist_eq_norm] at this
  simpa [norm_smul, abs_of_nonneg hs0, mul_assoc] using this

theorem sufficient_decrease_core {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, f (x (k + 1)) ≤ Shared.costC f x η k - beta p c₁ c₂ L * ‖gradient f (x k)‖ ^ 2 := by
  have hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0 := by
    intro k; have := (hdir k).1; nlinarith [sq_nonneg ‖gradient f (x k)‖]
  exact nls_sd_core p r f (hf.differentiable one_ne_zero) x d α η hrun c₁ c₂ hc₁ hc₂ hdir hαμ L
    (by exact_mod_cast hL) (nls_HL_of_Lbar p r f x d α η hrun hdesc L hLip)

theorem cost_contraction_core {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, Shared.costC f x η (k + 1) - f xstar ≤
      theta p c₁ c₂ L γ * (Shared.costC f x η k - f xstar) := by
  have hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0 := by
    intro k; have := (hdir k).1; nlinarith [sq_nonneg ‖gradient f (x k)‖]
  exact nls_contract_core p r f (hf.differentiable one_ne_zero) γ hsc xstar hmin hηmax x d α η hrun
    c₁ c₂ hc₁ hc₂ hdir hαμ L (by exact_mod_cast hL)
    (nls_HL_of_Lbar p r f x d α η hrun hdesc L hLip)

theorem r_linear_convergence_core {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdir : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (hLip : ∀ S : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded S →
      ∃ L : ℝ≥0, LipschitzOnWith L (gradient f) S) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ k, f (x k) - f xstar ≤ θ ^ k * (f (x 0) - f xstar) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hdir⟩ := hdir
  have hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0 := by
    intro k; have := (hdir k).1; nlinarith [sq_nonneg ‖gradient f (x k)‖]
  have hbasic := nls_cost_basic p r f x d α η hrun hdesc
  have hlev := nls_level p r f x d α η hrun hdesc
  have hγ := hsc.1
  set A := f (x 0) - f xstar with hA
  set G0 := ‖gradient f xstar‖ with hG0
  have hA0 : 0 ≤ A := by have := hmin (x 0); linarith
  set R := max 1 (2 * γ * (A + G0)) with hR
  have hball : ∀ k, ‖x k - xstar‖ ≤ R := by
    intro k
    have h1 := hsc.2 (x k) xstar
    have h2 : -(G0 * ‖x k - xstar‖) ≤ ⟪gradient f xstar, x k - xstar⟫_ℝ := by
      have := abs_real_inner_le_norm (gradient f xstar) (x k - xstar)
      rw [abs_le] at this; linarith [this.1]
    set ρ := ‖x k - xstar‖
    have hρ0 : 0 ≤ ρ := norm_nonneg _
    have h3 : ρ ^ 2 ≤ 2 * γ * (A + G0 * ρ) := by
      have h4 : 1 / (2 * γ) * ρ ^ 2 ≤ A + G0 * ρ := by linarith [hlev k, hA]
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)] at h4; linarith
    rcases le_or_gt ρ 1 with h | h
    · exact le_trans h (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      have hG0n : 0 ≤ G0 := norm_nonneg _
      have h5 : ρ * ρ ≤ (2 * γ * (A + G0)) * ρ := by
        nlinarith [mul_nonneg (mul_nonneg hγ.le hA0) (sub_nonneg.2 h.le)]
      exact le_of_mul_le_mul_right h5 (by linarith)
  have hR0 : 0 ≤ R := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨L0, hL0⟩ := hLip (Metric.closedBall xstar R) Metric.isBounded_closedBall
  have hgb : ∀ k, ‖gradient f (x k)‖ ≤ G0 + L0 * R := by
    intro k
    have hm1 : x k ∈ Metric.closedBall xstar R := by rw [Metric.mem_closedBall, dist_eq_norm]; exact hball k
    have hm2 : xstar ∈ Metric.closedBall xstar R := Metric.mem_closedBall_self hR0
    have := hL0.dist_le_mul _ hm1 _ hm2
    rw [dist_eq_norm, dist_eq_norm] at this
    have h3 := norm_le_norm_sub_add (gradient f (x k)) (gradient f xstar)
    have h4 : (L0 : ℝ) * ‖x k - xstar‖ ≤ L0 * R := mul_le_mul_of_nonneg_left (hball k) L0.2
    linarith
  set D := c₂ * (G0 + L0 * R) with hD
  have hdb : ∀ k, ‖d k‖ ≤ D := fun k => le_trans (hdir k).2 (mul_le_mul_of_nonneg_left (hgb k) hc₂.le)
  obtain ⟨L1, hL1⟩ := hLip (Metric.closedBall xstar (R + p.μ * D)) Metric.isBounded_closedBall
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) (hdb 0)
  have hμ := p.μ_pos
  have mem : ∀ k s, 0 ≤ s → s ≤ p.μ → x k + s • d k ∈ Metric.closedBall xstar (R + p.μ * D) := by
    intro k s hs0 hsμ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : x k + s • d k - xstar = (x k - xstar) + s • d k := by abel
    rw [e]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_of_nonneg hs0]
    have := mul_le_mul hsμ (hdb k) (norm_nonneg _) hμ.le
    linarith [hball k]
  set L : ℝ := (L1 : ℝ) + 1 with hLdef
  have hL : 0 < L := by have := L1.2; positivity
  have HL : ∀ k s, 0 ≤ s → s ≤ p.μ →
      ‖gradient f (x k + s • d k) - gradient f (x k)‖ ≤ L * s * ‖d k‖ := by
    intro k s hs0 hsμ
    have h2 := mem k 0 le_rfl hμ.le
    simp only [zero_smul, add_zero] at h2
    have := hL1.dist_le_mul _ (mem k s hs0 hsμ) _ h2
    rw [dist_eq_norm, dist_eq_norm] at this
    have e : x k + s • d k - x k = s • d k := by abel
    rw [e, norm_smul, Real.norm_of_nonneg hs0] at this
    have h5 : (L1 : ℝ) * (s * ‖d k‖) ≤ L * s * ‖d k‖ := by
      rw [hLdef]; nlinarith [mul_nonneg hs0 (norm_nonneg (d k))]
    linarith
  have hcon := nls_contract_core p r f (hf.differentiable one_ne_zero) γ hsc xstar hmin hηmax x d α η
    hrun c₁ c₂ hc₁ hc₂ hdir hαμ L hL HL
  obtain ⟨hθ0, hθ1⟩ := nls_theta_bounds p c₁ c₂ L γ hc₁ hc₂ hL hγ hηmax
  refine ⟨theta p c₁ c₂ L γ, hθ0, hθ1, ?_⟩
  have hind : ∀ k, Shared.costC f x η k - f xstar ≤
      theta p c₁ c₂ L γ ^ k * (f (x 0) - f xstar) := by
    intro k
    induction k with
    | zero => simp [Shared.costC]
    | succ k ih =>
      calc Shared.costC f x η (k + 1) - f xstar
          ≤ theta p c₁ c₂ L γ * (Shared.costC f x η k - f xstar) := hcon k
        _ ≤ theta p c₁ c₂ L γ * (theta p c₁ c₂ L γ ^ k * (f (x 0) - f xstar)) :=
            mul_le_mul_of_nonneg_left ih hθ0.le
        _ = _ := by ring
  intro k
  linarith [hind k, (hbasic k).1]

end NonmonotoneLS.RLinear

open NonmonotoneLS.RLinear
open NonmonotoneLS NonmonotoneLS.RLinear

theorem solution {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (γ : ℝ) (hsc : IsStronglyConvexWith f γ)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (hηmax : p.ηmax < 1)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, Shared.costC f x η (k + 1) - f xstar ≤
      theta p c₁ c₂ L γ * (Shared.costC f x η k - f xstar) := by
  exact cost_contraction_core p r f hf γ hsc xstar hmin hηmax x d α η hrun c₁ c₂ hc₁ hc₂ hdir hαμ L hL hLip
