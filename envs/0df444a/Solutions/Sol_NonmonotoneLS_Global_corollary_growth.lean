-- Prove2me | solution 1 for NonmonotoneLS.Global.corollary_growth
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:05:47.524802+00:00
-- url     : https://prove2.me/submissions/c4cf745a-8a8a-4f91-8054-49ea782f49a3

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

lemma nls_Lbar_mem (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    ∀ k s, 0 ≤ s → s ≤ p.μ → x k + s • d k ∈ Lbar p f x d := by
  have hlev := nls_level p r f x d α η hrun hdesc
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

/-- unified step lower bound along a run -/
lemma nls_run_lb (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzHyp p r f x d L) (k : ℕ) :
    min (p.μ / p.ρ) (min (2 * (1 - p.δ) / ((L:ℝ) * p.ρ)) ((1 - p.σ) / (L:ℝ)) *
      (|⟪gradient f (x k), d k⟫_ℝ| / ‖d k‖ ^ 2)) ≤ α k := by
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hX : 0 ≤ |⟪gradient f (x k), d k⟫_ℝ| / ‖d k‖ ^ 2 := by positivity
  cases r with
  | wolfe =>
    have hst : Shared.IsWolfeStep p f (x k) (d k) (Shared.costC f x η k) (α k) := hrun.step k
    have hlev := nls_level p Rule.wolfe f x d α η hrun hdesc
    have hL1 : LipschitzOnWith L (gradient f) (levelSet f (x 0)) := hLip
    have hm1 : x k + α k • d k ∈ levelSet f (x 0) := by
      rw [← hrun.update k]; exact hlev (k+1)
    have := hL1.dist_le_mul _ hm1 _ (hlev k)
    rw [dist_eq_norm, dist_eq_norm] at this
    have hw := wolfe_lb_core p f (x k) (d k) _ (α k) L hL' (hdesc k) hst this
    refine le_trans (min_le_right _ _) (le_trans ?_ hw)
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) hX
  | armijo =>
    have hst : Shared.IsArmijoStep p f (x k) (d k) (Shared.costC f x η k) (α k) := hrun.step k
    have hL1 : LipschitzOnWith L (gradient f) (Lbar p f x d) := hLip
    have hmem := nls_Lbar_mem p Rule.armijo f x d α η hrun hdesc k
    have hfC := (nls_cost_basic p Rule.armijo f x d α η hrun hdesc k).1
    have hlip : p.ρ * α k ≤ p.μ → ∀ y ∈ segment ℝ (x k) (x k + (p.ρ * α k) • d k),
        ‖gradient f y - gradient f (x k)‖ ≤ (L:ℝ) * ‖y - x k‖ := by
      intro hle y hy
      rw [segment_eq_image'] at hy
      obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hy
      have hα := (nls_step_facts p Rule.armijo f x d α η hrun k).1
      have hρ : 0 < p.ρ := by linarith [p.one_lt_ρ]
      have e : x k + θ • (x k + (p.ρ * α k) • d k - x k) = x k + (θ * (p.ρ * α k)) • d k := by
        rw [add_sub_cancel_left, smul_smul]
      dsimp only
      rw [e]
      have hs0 : 0 ≤ θ * (p.ρ * α k) := by positivity
      have hs1 : θ * (p.ρ * α k) ≤ p.μ := by nlinarith [mul_pos hρ hα]
      have := hL1.dist_le_mul _ (hmem _ hs0 hs1) _ (by simpa using hmem 0 le_rfl p.μ_pos.le)
      rw [dist_eq_norm, dist_eq_norm] at this
      exact this
    have ha := armijo_lb_core p f hf (x k) (d k) _ (α k) L hL' (hdesc k) hfC hst hlip
    refine le_trans (min_le_min le_rfl ?_) ha
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hX

lemma nls_run_dec (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzHyp p r f x d L) (k : ℕ) :
    f (x (k + 1)) ≤ Shared.costC f x η k - p.δ * min (p.μ / p.ρ)
      (min (2 * (1 - p.δ) / ((L:ℝ) * p.ρ)) ((1 - p.σ) / (L:ℝ)) *
      (|⟪gradient f (x k), d k⟫_ℝ| / ‖d k‖ ^ 2)) * |⟪gradient f (x k), d k⟫_ℝ| := by
  have hlb := nls_run_lb p r f hf x d α η hrun hdesc L hL hLip k
  obtain ⟨-, hs⟩ := nls_step_facts p r f x d α η hrun k
  rw [abs_of_nonpos (hdesc k)] at hlb ⊢
  have h1 := mul_le_mul_of_nonneg_right hlb (neg_nonneg.2 (hdesc k))
  have := mul_le_mul_of_nonneg_left h1 p.δ_pos.le
  nlinarith

lemma nls_C_dec {E : Type*} (f : E → ℝ) (x : ℕ → E) (η : ℕ → ℝ) (hη : ∀ k, 0 ≤ η k) (k : ℕ)
    (D : ℝ) (h : f (x (k + 1)) ≤ Shared.costC f x η k - D) :
    Shared.costC f x η (k + 1) ≤ Shared.costC f x η k - D / Shared.costQ η (k + 1) := by
  have hC := nls_C_succ f x η hη k
  have hQ := nls_Q_ge_one η hη (k+1)
  have hQ1 : Shared.costQ η (k+1) = η k * Shared.costQ η k + 1 := rfl
  have hpos : 0 < Shared.costQ η (k+1) := by linarith
  have h2 : D ≤ (Shared.costC f x η k - Shared.costC f x η (k + 1)) * Shared.costQ η (k+1) := by
    rw [hQ1] at hC ⊢; nlinarith
  have := (div_le_iff₀ hpos).2 h2
  linarith

lemma nls_tele (C u : ℕ → ℝ) (m : ℝ) (K : ℕ) (hu : ∀ k, 0 ≤ u k) (hm : ∀ k, m ≤ C k)
    (h : ∀ k, K ≤ k → C (k + 1) ≤ C k - u k) : Summable u := by
  rw [← summable_nat_add_iff K]
  apply summable_of_sum_range_le (c := C K - m) (fun k => hu _)
  intro N
  have : ∀ N, ∑ i ∈ Finset.range N, u (i + K) ≤ C K - C (N + K) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := h (N + K) (by omega)
      rw [show N + 1 + K = N + K + 1 by ring]
      linarith
  linarith [this N, hm (N + K)]

theorem sufficient_decrease_core {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (K : ℕ)
    (hdir : ∀ k, K ≤ k →
      ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
        ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzHyp p r f x d L) :
    ∀ k, K ≤ k →
      f (x (k + 1)) ≤ Shared.costC f x η k -
        min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / ((L : ℝ) * p.ρ * c₂ ^ 2)))
            (p.δ * (1 - p.σ) * c₁ ^ 2 / ((L : ℝ) * c₂ ^ 2)) *
          ‖gradient f (x k)‖ ^ 2 := by
  intro k hk
  have hdec := nls_run_dec p r f hf x d α η hrun hdesc L hL hLip k
  obtain ⟨h1, h2⟩ := hdir k hk
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  set g := gradient f (x k)
  set β := min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / ((L : ℝ) * p.ρ * c₂ ^ 2)))
            (p.δ * (1 - p.σ) * c₁ ^ 2 / ((L : ℝ) * c₂ ^ 2)) with hβ
  have hδ := p.δ_pos
  have hσ1 := p.σ_lt_one
  have hδσ := p.δ_lt_σ
  have hρ := p.one_lt_ρ
  have hμ := p.μ_pos
  have hβ0 : 0 ≤ β := by
    have h1' : 0 < 1 - p.δ := by linarith
    have h2' : 0 < 1 - p.σ := by linarith
    have : (0:ℝ) < p.ρ := by linarith
    refine le_min (le_min ?_ ?_) ?_ <;> positivity
  rcases eq_or_lt_of_le (norm_nonneg g) with hg0 | hgpos
  · rw [← hg0]
    have hm : 0 ≤ p.δ * min (p.μ / p.ρ) (min (2 * (1 - p.δ) / ((L:ℝ) * p.ρ)) ((1 - p.σ) / (L:ℝ)) *
      (|⟪g, d k⟫_ℝ| / ‖d k‖ ^ 2)) * |⟪g, d k⟫_ℝ| := by
      have : (0:ℝ) < p.ρ := by linarith
      have h1' : 0 < 1 - p.δ := by linarith
      have h2' : 0 < 1 - p.σ := by linarith
      refine mul_nonneg (mul_nonneg hδ.le (le_min (by positivity) ?_)) (abs_nonneg _)
      exact mul_nonneg (le_min (by positivity) (by positivity)) (by positivity)
    simp; linarith
  have hG2 : 0 < ‖g‖ ^ 2 := by positivity
  have hgd : c₁ * ‖g‖ ^ 2 ≤ |⟪g, d k⟫_ℝ| := by
    rw [abs_of_nonpos (hdesc k)]; linarith
  have hdd : ‖d k‖ ^ 2 ≤ c₂ ^ 2 * ‖g‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hdpos : 0 < ‖d k‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (d k)) with h | h
    · exfalso
      have : d k = 0 := norm_eq_zero.1 h.symm
      rw [this, inner_zero_right] at hgd
      simp at hgd; nlinarith [mul_pos hc₁ hG2]
    · exact h
  -- X ≥ c₁ / c₂²
  have hX : c₁ / c₂ ^ 2 ≤ |⟪g, d k⟫_ℝ| / ‖d k‖ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul hgd hdd (by positivity) (abs_nonneg _)
    nlinarith
  set X := |⟪g, d k⟫_ℝ| / ‖d k‖ ^ 2
  set A := |⟪g, d k⟫_ℝ|
  -- show β ≤ δ * m * c₁ where m is the min
  set c := min (2 * (1 - p.δ) / ((L:ℝ) * p.ρ)) ((1 - p.σ) / (L:ℝ))
  set m := min (p.μ / p.ρ) (c * X)
  have hρ0 : (0:ℝ) < p.ρ := by linarith
  have hm0 : 0 ≤ m := by
    have h1' : 0 < 1 - p.δ := by linarith
    have h2' : 0 < 1 - p.σ := by linarith
    exact le_min (by positivity) (mul_nonneg (le_min (by positivity) (by positivity)) (by positivity))
  suffices key : β ≤ p.δ * m * c₁ by
    have e2 := mul_le_mul_of_nonneg_right key hG2.le
    have e3 : p.δ * m * (c₁ * ‖g‖ ^ 2) ≤ p.δ * m * A :=
      mul_le_mul_of_nonneg_left hgd (by positivity)
    nlinarith
  rcases min_cases (p.μ / p.ρ) (c * X) with ⟨hmv, -⟩ | ⟨hmv, -⟩
  · rw [show m = p.μ / p.ρ from hmv]
    refine le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_of_eq ?_))
    field_simp
  · rw [show m = c * X from hmv]
    have hcX : c * (c₁ / c₂ ^ 2) ≤ c * X := by
      apply mul_le_mul_of_nonneg_left hX
      have h1' : 0 < 1 - p.δ := by linarith
      have h2' : 0 < 1 - p.σ := by linarith
      exact le_min (by positivity) (by positivity)
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcX hδ.le) hc₁.le)
    rcases min_cases (2 * (1 - p.δ) / ((L:ℝ) * p.ρ)) ((1 - p.σ) / (L:ℝ)) with ⟨hcv, -⟩ | ⟨hcv, -⟩
    · rw [show c = 2 * (1 - p.δ) / ((L:ℝ) * p.ρ) from hcv]
      refine le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_of_eq ?_))
      field_simp
    · rw [show c = (1 - p.σ) / (L:ℝ) from hcv]
      refine le_trans (min_le_right _ _) (le_of_eq ?_)
      field_simp


lemma nls_lip_pos (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    ∃ L : ℝ≥0, 0 < L ∧ LipschitzHyp p r f x d L := by
  obtain ⟨L, hL⟩ := hLip
  refine ⟨L + 1, by positivity, ?_⟩
  cases r with
  | wolfe => exact LipschitzOnWith.weaken hL (le_add_of_nonneg_right zero_le_one)
  | armijo => exact LipschitzOnWith.weaken hL (le_add_of_nonneg_right zero_le_one)

theorem summable_core {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (hdir : DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    Summable (fun k => ‖gradient f (x k)‖ ^ 2 / Shared.costQ η (k + 1)) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hev⟩ := hdir
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  obtain ⟨L, hL, hLip⟩ := nls_lip_pos p r f x d hLip
  have hsd := sufficient_decrease_core p r f hf x d α η hrun hdesc c₁ c₂ hc₁ hc₂ K hK L hL hLip
  set β := min (min (p.δ * p.μ * c₁ / p.ρ) (2 * p.δ * (1 - p.δ) * c₁ ^ 2 / ((L : ℝ) * p.ρ * c₂ ^ 2)))
            (p.δ * (1 - p.σ) * c₁ ^ 2 / ((L : ℝ) * c₂ ^ 2)) with hβ
  have hβ0 : 0 < β := by
    have hδ := p.δ_pos
    have h1' : 0 < 1 - p.δ := by linarith [p.δ_lt_σ, p.σ_lt_one]
    have h2' : 0 < 1 - p.σ := by linarith [p.σ_lt_one]
    have : (0:ℝ) < p.ρ := by linarith [p.one_lt_ρ]
    have := p.μ_pos
    have hL' : (0:ℝ) < L := by exact_mod_cast hL
    refine lt_min (lt_min ?_ ?_) ?_ <;> positivity
  have hη : ∀ k, 0 ≤ η k := fun k => le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  obtain ⟨m, hm⟩ := hbdd
  have hb := nls_cost_basic p r f x d α η hrun hdesc
  have hQ : ∀ k, 0 < Shared.costQ η k := fun k => by linarith [nls_Q_ge_one η hη k]
  have hs := nls_tele (Shared.costC f x η)
    (fun k => β * (‖gradient f (x k)‖ ^ 2 / Shared.costQ η (k + 1))) m K
    (fun k => mul_nonneg hβ0.le (div_nonneg (sq_nonneg _) (hQ _).le))
    (fun k => le_trans (hm ⟨x k, rfl⟩) (hb k).1)
    (fun k hk => by
      have := nls_C_dec f x η hη k _ (hsd k hk)
      rw [mul_div_assoc] at this; exact this)
  exact (summable_mul_left_iff hβ0.ne').1 hs

theorem global_convergence_core {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (hdir : DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (p.ηmax < 1 → Tendsto (fun k => gradient f (x k)) atTop (𝓝 0)) ∧
      (p.ηmax < 1 → ∀ xstar : EuclideanSpace ℝ (Fin n),
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 xstar)) →
          gradient f xstar = 0) := by
  have hs := summable_core p r f hf hbdd x d α η hrun hdesc hdir hLip
  have hη : ∀ k, 0 ≤ η k := fun k => le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  have hQ : ∀ k, 0 < Shared.costQ η k := fun k => by linarith [nls_Q_ge_one η hη k]
  have part2 : p.ηmax < 1 → Tendsto (fun k => gradient f (x k)) atTop (𝓝 0) := by
    intro hηmax
    have hηle : ∀ k, 0 ≤ η k ∧ η k ≤ p.ηmax := fun k => ⟨hη k, (hrun.eta_mem k).2⟩
    have hs2 : Summable (fun k => (1 - p.ηmax) * ‖gradient f (x k)‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun k => mul_nonneg (by linarith) (sq_nonneg _)) ?_ hs
      intro k
      have := nls_Q_le η p.ηmax hηle p.ηmax_le_one (k+1)
      rw [le_div_iff₀ (hQ _)]
      have h0 : 0 ≤ ‖gradient f (x k)‖ ^ 2 := sq_nonneg _
      nlinarith
    have hs3 := (summable_mul_left_iff (by linarith : (1 - p.ηmax) ≠ 0)).1 hs2
    have ht := hs3.tendsto_atTop_zero
    have ht2 : Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp ht
      rw [Real.sqrt_zero] at this
      refine this.congr (fun k => ?_)
      simp [Real.sqrt_sq (norm_nonneg _)]
    exact tendsto_zero_iff_norm_tendsto_zero.2 ht2
  refine ⟨?_, part2, ?_⟩
  · intro ε hε
    by_contra hcon
    rw [Filter.not_frequently] at hcon
    obtain ⟨N, hN⟩ := eventually_atTop.1 hcon
    have hη1 : ∀ k, 0 ≤ η k ∧ η k ≤ 1 :=
      fun k => ⟨hη k, le_trans (hrun.eta_mem k).2 p.ηmax_le_one⟩
    have hs' := (summable_nat_add_iff N).2 hs
    have h1 : Summable (fun k : ℕ => ε ^ 2 * (((k + (N + 2) : ℕ) : ℝ))⁻¹) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) ?_ hs'
      intro k
      have hg := not_lt.1 (hN (k + N) (by omega))
      have hQle := nls_Q_le_succ η hη1 (k + N + 1)
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (hQ _)]
      have : ε ^ 2 ≤ ‖gradient f (x (k + N))‖ ^ 2 := pow_le_pow_left₀ hε.le hg 2
      push_cast at hQle ⊢
      have hQ0 := hQ (k + N + 1)
      nlinarith [sq_nonneg ε]
    have h2 := (summable_mul_left_iff (by positivity : ε ^ 2 ≠ 0)).1 h1
    have h3 := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ))⁻¹) (N + 2)).1 h2
    exact Real.not_summable_natCast_inv h3
  · intro hηmax xstar ⟨φ, hφ, hx⟩
    have hcont : Continuous (gradient f) := by
      show Continuous (fun y => (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ f y))
      exact (InnerProductSpace.toDual ℝ _).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
    have h1 : Tendsto (fun k => gradient f (x (φ k))) atTop (𝓝 (gradient f xstar)) :=
      (hcont.tendsto xstar).comp hx
    have h2 : Tendsto (fun k => gradient f (x (φ k))) atTop (𝓝 0) :=
      (part2 hηmax).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2


theorem step_exists_core {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : EuclideanSpace ℝ (Fin n)) (C : ℝ) (hC : f x ≤ C)
    (hdesc : ⟪gradient f x, d⟫_ℝ < 0) :
    (∃ α : ℝ, Shared.IsWolfeStep p f x d C α) ∧
      ∀ αbar : ℝ, 0 < αbar → ∃ h : ℤ, IsGreatest (Shared.armijoAdmissible p f x d C αbar) h := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  set g := ⟪gradient f x, d⟫_ℝ with hg
  set φ : ℝ → ℝ := fun t => f (x + t • d) with hφ
  have hδ := p.δ_pos
  have hδσ := p.δ_lt_σ
  have hσ1 := p.σ_lt_one
  have hρ1 := p.one_lt_ρ
  have hρ0 : (0:ℝ) < p.ρ := by linarith
  have hμ := p.μ_pos
  have hder : ∀ t, HasDerivAt φ ⟪gradient f (x + t • d), d⟫_ℝ t :=
    fun t => nls_hasDerivAt_line f hfd x d t
  have hφ0 : φ 0 = f x := by simp [hφ]
  -- small steps satisfy strict sufficient decrease w.r.t. f x
  have Esmall : ∀ᶠ t in 𝓝[>] (0:ℝ), φ t < f x + p.δ * t * g := by
    have h1 := hasDerivAt_iff_tendsto_slope.1 (hder 0)
    simp only [zero_smul, add_zero] at h1
    have h2 : Tendsto (slope φ 0) (𝓝[>] (0:ℝ)) (𝓝 g) :=
      h1.mono_left (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))
    have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), slope φ 0 t < p.δ * g :=
      h2 (Iio_mem_nhds (by nlinarith))
    filter_upwards [h3, self_mem_nhdsWithin] with t ht htpos
    have htpos' : (0:ℝ) < t := htpos
    rw [slope_def_field, sub_zero, hφ0, div_lt_iff₀ htpos'] at ht
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm⟩ := hbdd
    have hmx : m ≤ f x := hm ⟨x, rfl⟩
    set t₁ := (C - m) / (p.δ * (-g)) + 1 with ht₁
    have hgneg : 0 < -g := by linarith
    have hq : 0 ≤ (C - m) / (p.δ * (-g)) := div_nonneg (by linarith) (by positivity)
    have ht₁pos : 0 < t₁ := by linarith
    set ψ : ℝ → ℝ := fun t => φ t - C - p.δ * t * g with hψ
    have hψder : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • d), d⟫_ℝ - p.δ * g) t := by
      intro t
      have := ((hder t).sub_const C).sub ((hasDerivAt_id t).const_mul (p.δ * g))
      refine (this.congr_deriv (by simp)).congr_of_eventuallyEq ?_
      filter_upwards with y; simp [hψ]; ring
    have hψcont : Continuous ψ := continuous_iff_continuousAt.2 (fun t => (hψder t).continuousAt)
    have hψt₁ : 0 < ψ t₁ := by
      have h1 : m ≤ φ t₁ := hm ⟨_, rfl⟩
      have h2 : p.δ * t₁ * g = -(p.δ * (-g)) * t₁ := by ring
      have h3 : p.δ * (-g) * ((C - m) / (p.δ * (-g))) = C - m :=
        mul_div_cancel₀ _ (by positivity)
      simp only [hψ]
      rw [h2]
      have : p.δ * (-g) * t₁ = C - m + p.δ * (-g) := by rw [ht₁, mul_add, h3, mul_one]
      nlinarith [mul_pos hδ hgneg]
    obtain ⟨t₀, ht₀, ht₀I⟩ := (Esmall.and (Ioo_mem_nhdsGT ht₁pos)).exists
    have hψt₀ : ψ t₀ < ψ 0 := by simp only [hψ, hφ0]; simp only [hφ] at ht₀ ⊢; simp; linarith
    obtain ⟨ξ, hξI, hξmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 ht₁pos.le)
      hψcont.continuousOn
    have hξt₀ : ψ ξ ≤ ψ t₀ := hξmin ⟨ht₀I.1.le, ht₀I.2.le⟩
    have hψ0 : ψ 0 ≤ 0 := by simp only [hψ, hφ0]; linarith
    have hξ0 : ξ ≠ 0 := by rintro rfl; linarith
    have hξ1 : ξ ≠ t₁ := by rintro rfl; linarith
    have hξI' : ξ ∈ Set.Ioo 0 t₁ :=
      ⟨lt_of_le_of_ne hξI.1 (Ne.symm hξ0), lt_of_le_of_ne hξI.2 hξ1⟩
    have hloc : IsLocalMin ψ ξ := hξmin.isLocalMin (Icc_mem_nhds hξI'.1 hξI'.2)
    have hd0 := hloc.hasDerivAt_eq_zero (hψder ξ)
    refine ⟨ξ, hξI'.1, ?_, ?_⟩
    · have : ψ ξ < 0 := by linarith
      simp only [hψ, hφ] at this; linarith
    · nlinarith
  · intro αbar hαbar
    apply Int.exists_greatest_of_bdd
    · obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (p.μ / αbar) hρ1
      refine ⟨N, fun z hz => ?_⟩
      by_contra hlt
      push_neg at hlt
      have h1 : p.ρ ^ (N : ℤ) ≤ p.ρ ^ z := zpow_le_zpow_right₀ hρ1.le hlt.le
      rw [zpow_natCast] at h1
      have h2 : p.μ < αbar * p.ρ ^ z := by
        rw [div_lt_iff₀ hαbar] at hN; nlinarith
      linarith [hz.2]
    · obtain ⟨ε, hε, hεsub⟩ := (nhdsGT_basis (0:ℝ)).eventually_iff.1 Esmall
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < min ε p.μ / αbar)
        (inv_lt_one_of_one_lt₀ hρ1)
      refine ⟨-(N:ℤ), ?_, ?_⟩
      · have ht : αbar * p.ρ ^ (-(N:ℤ)) < min ε p.μ := by
          rw [zpow_neg, zpow_natCast, ← inv_pow]
          rw [lt_div_iff₀ hαbar] at hN; linarith
        have htpos : 0 < αbar * p.ρ ^ (-(N:ℤ)) := mul_pos hαbar (zpow_pos hρ0 _)
        have := hεsub ⟨htpos, lt_of_lt_of_le ht (min_le_left _ _)⟩
        simp only [hφ] at this
        linarith
      · have ht : αbar * p.ρ ^ (-(N:ℤ)) < min ε p.μ := by
          rw [zpow_neg, zpow_natCast, ← inv_pow]
          rw [lt_div_iff₀ hαbar] at hN; linarith
        exact le_trans ht.le (min_le_right _ _)


lemma nls_tmono (δ A c a₀ a T : ℝ) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hT : 0 < T)
    (ha₀ : 0 ≤ a₀) (ha : a₀ ≤ a) :
    δ * min (A * a₀) (c * a₀ ^ 2 / T) ≤ δ * min (A * a) (c * a ^ 2 / T) := by
  apply mul_le_mul_of_nonneg_left _ hδ
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left ha hA
  · apply div_le_div_of_nonneg_right _ hT.le
    apply mul_le_mul_of_nonneg_left _ hc
    exact pow_le_pow_left₀ ha₀ ha 2

theorem corollary_core {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η) (hηmax : p.ηmax < 1)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hdir : ∀ᶠ k in atTop, ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2)
    (τ₁ τ₂ : ℝ) (hτ₁ : 0 < τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgrowth : ∀ k : ℕ, ‖d k‖ ^ 2 ≤ τ₁ + τ₂ * k)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (τ₂ ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (τ₂ = 0 → Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hdir
  obtain ⟨L, hL, hLip⟩ := nls_lip_pos p r f x d hLip
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hδ := p.δ_pos
  have h1δ : 0 < 1 - p.δ := by linarith [p.δ_lt_σ, p.σ_lt_one]
  have h1σ : 0 < 1 - p.σ := by linarith [p.σ_lt_one]
  have hρ0 : (0:ℝ) < p.ρ := by linarith [p.one_lt_ρ]
  have hμ := p.μ_pos
  set c := min (2 * (1 - p.δ) / ((L:ℝ) * p.ρ)) ((1 - p.σ) / (L:ℝ)) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by positivity)
  set A := p.μ / p.ρ with hA
  have hA0 : 0 < A := by positivity
  set T : ℕ → ℝ := fun k => τ₁ + τ₂ * k with hT
  have hT0 : ∀ k, 0 < T k := fun k => by simp only [hT]; positivity
  set a : ℕ → ℝ := fun k => c₁ * ‖gradient f (x k)‖ ^ 2 with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => by simp only [ha]; positivity
  set t : ℕ → ℝ := fun k => p.δ * min (A * a k) (c * a k ^ 2 / T k) with ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => by
    simp only [ht]
    exact mul_nonneg hδ.le (le_min (mul_nonneg hA0.le (ha0 k))
      (div_nonneg (mul_nonneg hc0.le (sq_nonneg _)) (hT0 k).le))
  have hη : ∀ k, 0 ≤ η k := fun k => le_trans p.ηmin_nonneg (hrun.eta_mem k).1
  have hηle : ∀ k, 0 ≤ η k ∧ η k ≤ p.ηmax := fun k => ⟨hη k, (hrun.eta_mem k).2⟩
  have hQ : ∀ k, 0 < Shared.costQ η k := fun k => by linarith [nls_Q_ge_one η hη k]
  -- decrease
  have hdec : ∀ k, K ≤ k → f (x (k + 1)) ≤ Shared.costC f x η k - t k := by
    intro k hk
    have h := nls_run_dec p r f hf x d α η hrun hdesc L hL hLip k
    set u := |⟪gradient f (x k), d k⟫_ℝ| with hu
    have hua : a k ≤ u := by
      simp only [ha, hu]; rw [abs_of_nonpos (hdesc k)]; linarith [hK k hk]
    have hX : u / T k ≤ u / ‖d k‖ ^ 2 := by
      rcases eq_or_ne (d k) 0 with hd | hd
      · have : u = 0 := by simp [hu, hd]
        simp [this]
      · apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (hgrowth k)
    have hu0 : 0 ≤ u := abs_nonneg _
    have key : t k ≤ p.δ * min A (c * (u / ‖d k‖ ^ 2)) * u := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hδ.le
      rw [min_mul_of_nonneg _ _ hu0]
      apply min_le_min
      · exact mul_le_mul_of_nonneg_left hua hA0.le
      · have e1 : c * a k ^ 2 / T k ≤ c * u ^ 2 / T k := by
          apply div_le_div_of_nonneg_right _ (hT0 k).le
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha0 k) hua 2) hc0.le
        have e2 : c * u ^ 2 / T k = c * (u / T k) * u := by ring
        have e3 : c * (u / T k) * u ≤ c * (u / ‖d k‖ ^ 2) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hc0.le) hu0
        linarith
    linarith
  obtain ⟨m, hm⟩ := hbdd
  have hb := nls_cost_basic p r f x d α η hrun hdesc
  have hsum : Summable (fun k => (1 - p.ηmax) * t k) := by
    refine nls_tele (Shared.costC f x η) _ m K (fun k => mul_nonneg (by linarith) (ht0 k))
      (fun k => le_trans (hm ⟨x k, rfl⟩) (hb k).1) (fun k hk => ?_)
    have h1 := nls_C_dec f x η hη k _ (hdec k hk)
    have h2 : (1 - p.ηmax) * t k ≤ t k / Shared.costQ η (k + 1) := by
      rw [le_div_iff₀ (hQ _)]
      have := nls_Q_le η p.ηmax hηle p.ηmax_le_one (k+1)
      nlinarith [ht0 k]
    linarith
  have hsum' := (summable_mul_left_iff (by linarith : (1 - p.ηmax) ≠ 0)).1 hsum
  refine ⟨fun _ ε hε => ?_, fun h0 => ?_⟩
  · by_contra hcon
    rw [Filter.not_frequently] at hcon
    obtain ⟨N, hN⟩ := eventually_atTop.1 hcon
    set a₀ := c₁ * ε ^ 2
    have ha₀ : 0 < a₀ := by positivity
    set B := p.δ * min (A * a₀ * τ₁) (c * a₀ ^ 2) / (τ₁ + τ₂)
    have hB : 0 < B := by
      have : 0 < min (A * a₀ * τ₁) (c * a₀ ^ 2) := lt_min (by positivity) (by positivity)
      positivity
    have hs' := (summable_nat_add_iff N).2 hsum'
    have h1 : Summable (fun k : ℕ => B * (((k + (N + 1) : ℕ) : ℝ))⁻¹) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs'
      have hg := not_lt.1 (hN (k + N) (by omega))
      have haa : a₀ ≤ a (k + N) := by
        simp only [ha]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hg 2) hc₁.le
      refine le_trans ?_ (nls_tmono p.δ A c a₀ _ _ hδ.le hA0.le hc0.le (hT0 _) ha₀.le haa)
      have hTk : T (k + N) ≤ (τ₁ + τ₂) * (((k + (N + 1) : ℕ) : ℝ)) := by
        simp only [hT]; push_cast; nlinarith
      have hTpos := hT0 (k + N)
      have hTge : τ₁ ≤ T (k + N) := by
        simp only [hT]
        have : (0:ℝ) ≤ ((k + N : ℕ) : ℝ) := by positivity
        nlinarith
      -- δ min(A a₀, c a₀²/T) ≥ δ min(A a₀ τ₁, c a₀²)/T ≥ B/(k+N+1)
      have hmin : min (A * a₀ * τ₁) (c * a₀ ^ 2) / T (k + N) ≤ min (A * a₀) (c * a₀ ^ 2 / T (k + N)) := by
        rw [div_le_iff₀ hTpos]
        rw [min_mul_of_nonneg _ _ hTpos.le]
        apply min_le_min
        · exact mul_le_mul_of_nonneg_left hTge (by positivity)
        · rw [div_mul_cancel₀ _ hTpos.ne']
      have hkpos : (0:ℝ) < (((k + (N + 1) : ℕ) : ℝ)) := by positivity
      have hM : 0 < min (A * a₀ * τ₁) (c * a₀ ^ 2) := lt_min (by positivity) (by positivity)
      have e1 : B * (((k + (N + 1) : ℕ) : ℝ))⁻¹ ≤ p.δ * (min (A * a₀ * τ₁) (c * a₀ ^ 2) / T (k + N)) := by
        rw [← div_eq_mul_inv]
        show p.δ * min (A * a₀ * τ₁) (c * a₀ ^ 2) / (τ₁ + τ₂) / (((k + (N + 1) : ℕ) : ℝ)) ≤ _
        rw [div_div, ← mul_div_assoc]
        exact div_le_div_of_nonneg_left (by positivity) hTpos hTk
      exact le_trans e1 (mul_le_mul_of_nonneg_left hmin hδ.le)
    have h2 := (summable_mul_left_iff hB.ne').1 h1
    have h3 := (summable_nat_add_iff (f := fun n : ℕ => ((n:ℝ))⁻¹) (N + 1)).1 h2
    exact Real.not_summable_natCast_inv h3
  · have htt := hsum'.tendsto_atTop_zero
    rw [tendsto_order]
    refine ⟨fun b hb => Eventually.of_forall (fun k => lt_of_lt_of_le hb (norm_nonneg _)), ?_⟩
    intro ε hε
    set a₀ := c₁ * ε ^ 2
    have ha₀ : 0 < a₀ := by positivity
    set v := p.δ * min (A * a₀) (c * a₀ ^ 2 / τ₁)
    have hv : 0 < v := by
      have : 0 < min (A * a₀) (c * a₀ ^ 2 / τ₁) := lt_min (by positivity) (by positivity)
      positivity
    filter_upwards [(tendsto_order.1 htt).2 v hv] with k hk
    by_contra hge
    have hg := not_lt.1 hge
    have haa : a₀ ≤ a k := by
      simp only [ha]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hg 2) hc₁.le
    have hTk : T k = τ₁ := by simp [hT, h0]
    have := nls_tmono p.δ A c a₀ _ _ hδ.le hA0.le hc0.le (hT0 k) ha₀.le haa
    rw [hTk] at this
    have : v ≤ t k := by simp only [ht, v]; rw [hTk]; exact this
    linarith

end NonmonotoneLS.Global

open NonmonotoneLS.Global
open NonmonotoneLS

theorem solution {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η) (hηmax : p.ηmax < 1)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (c₁ : ℝ) (hc₁ : 0 < c₁)
    (hdir : ∀ᶠ k in atTop, ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2)
    (τ₁ τ₂ : ℝ) (hτ₁ : 0 < τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgrowth : ∀ k : ℕ, ‖d k‖ ^ 2 ≤ τ₁ + τ₂ * k)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (τ₂ ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (τ₂ = 0 → Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0)) := by
  exact corollary_core p r f hf hbdd x d α η hrun hηmax hdesc c₁ hc₁ hdir τ₁ τ₂ hτ₁ hτ₂ hgrowth hLip
