-- Prove2me | solution 1 for MellinStrip.expDecay_strip
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T07:25:16.573633+00:00
-- url     : https://prove2.me/submissions/a3606423-dcb4-4c89-971a-458f013c0f87

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace B1Aux

def P (I : Set ℝ) (ψ : ℝ → ℂ) : Prop :=
  ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ, g x = (Real.exp (a * x) : ℂ) * ψ x

lemma psi_eq {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) (x : ℝ) :
    ψ x = (Real.exp (-(a * x)) : ℂ) * g x := by
  rw [hg, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
    Complex.ofReal_one, one_mul]

lemma psi_funext {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) :
    ψ = fun x => (Real.exp (-(a * x)) : ℂ) * g x := funext (psi_eq hg)

lemma continuous_psi {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) : Continuous ψ := by
  rw [psi_funext hg]
  exact Continuous.mul (by fun_prop) g.continuous

lemma norm_cexp_mul (s : ℂ) (x : ℝ) : ‖Complex.exp (s * x)‖ = Real.exp (s.re * x) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma norm_integrand {σ : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (σ * x) : ℂ) * ψ x) {s : ℂ} (hs : s.re = σ) (x : ℝ) :
    ‖ψ x * Complex.exp (s * x)‖ = ‖g x‖ := by
  rw [norm_mul, norm_cexp_mul, hg, norm_mul, hs, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]

lemma integrable_of {σ : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (σ * x) : ℂ) * ψ x) {s : ℂ} (hs : s.re = σ) :
    Integrable (fun x : ℝ => ψ x * Complex.exp (s * x)) := by
  refine Integrable.mono' g.integrable.norm ?_
    (Filter.Eventually.of_forall fun x => le_of_eq (norm_integrand hg hs x))
  exact ((continuous_psi hg).mul (by fun_prop)).aestronglyMeasurable

lemma exp_le_add (a b σ x : ℝ) (h1 : a ≤ σ) (h2 : σ ≤ b) :
    Real.exp (σ * x) ≤ Real.exp (a * x) + Real.exp (b * x) := by
  rcases le_total 0 x with hx | hx
  · have : Real.exp (σ * x) ≤ Real.exp (b * x) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 hx)
    linarith [Real.exp_pos (a * x)]
  · have : Real.exp (σ * x) ≤ Real.exp (a * x) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 hx)
    linarith [Real.exp_pos (b * x)]

lemma norm_le_sum {a b σ : ℝ} {ψ : ℝ → ℂ} {ga gb : SchwartzMap ℝ ℂ}
    (ha : ∀ x, ga x = (Real.exp (a * x) : ℂ) * ψ x) (hb : ∀ x, gb x = (Real.exp (b * x) : ℂ) * ψ x)
    (h1 : a ≤ σ) (h2 : σ ≤ b) (x : ℝ) :
    ‖ψ x‖ * Real.exp (σ * x) ≤ ‖ga x‖ + ‖gb x‖ := by
  rw [ha, hb, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  have := exp_le_add a b σ x h1 h2
  nlinarith [norm_nonneg (ψ x)]

lemma hasDerivAt_psi {a : ℝ} {ψ : ℝ → ℂ} {g : SchwartzMap ℝ ℂ}
    (hg : ∀ x, g x = (Real.exp (a * x) : ℂ) * ψ x) (x : ℝ) :
    HasDerivAt ψ (((Real.exp (-(a * x)) * -(a * 1) : ℝ) : ℂ) * g x +
      (Real.exp (-(a * x)) : ℂ) * deriv g x) x := by
  rw [psi_funext hg]
  have h1 : HasDerivAt (fun x : ℝ => (Real.exp (-(a * x)) : ℂ))
      ((Real.exp (-(a * x)) * -(a * 1) : ℝ) : ℂ) x :=
    (((hasDerivAt_id x).const_mul a).neg.exp).ofReal_comp
  exact h1.mul (g.hasDerivAt x)

lemma P_deriv {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) : P I (deriv ψ) := by
  intro a ha
  obtain ⟨g, hg⟩ := hP a ha
  refine ⟨SchwartzMap.derivCLM ℂ ℂ g - (a : ℂ) • g, fun x => ?_⟩
  rw [(hasDerivAt_psi hg x).deriv]
  simp only [SchwartzMap.sub_apply, SchwartzMap.derivCLM_apply, SchwartzMap.smul_apply,
    smul_eq_mul]
  have he : (Real.exp (a * x) : ℂ) * (Real.exp (-(a * x)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  push_cast
  push_cast at he
  linear_combination (-(deriv g x - (a : ℂ) * g x)) * he

lemma differentiable_of_P {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) (hne : I.Nonempty) :
    Differentiable ℝ ψ := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨g, hg⟩ := hP a ha
  exact fun x => (hasDerivAt_psi hg x).differentiableAt

lemma ibp {I : Set ℝ} {ψ : ℝ → ℂ} (hP : P I ψ) {s : ℂ} (hs : s.re ∈ I) :
    s * ∫ x : ℝ, ψ x * Complex.exp (s * x) = -∫ x : ℝ, deriv ψ x * Complex.exp (s * x) := by
  obtain ⟨g, hg⟩ := hP _ hs
  obtain ⟨g', hg'⟩ := P_deriv hP _ hs
  have hd := differentiable_of_P hP ⟨_, hs⟩
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (s * x)) (s * Complex.exp (s * x)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp
    have := (h0.const_mul s).cexp
    convert this using 1
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := ψ) (u' := deriv ψ)
    (v := fun x : ℝ => Complex.exp (s * x)) (v' := fun x : ℝ => s * Complex.exp (s * x))
    (fun x _ => (hd x).hasDerivAt) (fun x _ => hv x)
    (by
      have := (integrable_of hg rfl).const_mul s
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (integrable_of hg' rfl) (integrable_of hg rfl)
  rw [← key, ← integral_const_mul]
  congr 1
  funext x
  ring

lemma strip_bound (I : Set ℝ) (N : ℕ) : ∀ ψ : ℝ → ℂ, P I ψ → ∀ a b : ℝ, Set.Icc a b ⊆ I →
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s ^ N * ∫ x : ℝ, ψ x * Complex.exp (s * x)‖ ≤ C := by
  induction N with
  | zero =>
    intro ψ hP a b hab
    by_cases h : a ≤ b
    · obtain ⟨ga, hga⟩ := hP a (hab ⟨le_refl a, h⟩)
      obtain ⟨gb, hgb⟩ := hP b (hab ⟨h, le_refl b⟩)
      refine ⟨∫ x, (‖ga x‖ + ‖gb x‖), fun s h1 h2 => ?_⟩
      rw [pow_zero, one_mul]
      refine norm_integral_le_of_norm_le (ga.integrable.norm.add gb.integrable.norm)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, norm_cexp_mul]
      exact norm_le_sum hga hgb h1 h2 x
    · exact ⟨0, fun s h1 h2 => absurd (h1.trans h2) h⟩
  | succ N ih =>
    intro ψ hP a b hab
    obtain ⟨C, hC⟩ := ih (deriv ψ) (P_deriv hP) a b hab
    refine ⟨C, fun s h1 h2 => ?_⟩
    have hs : s.re ∈ I := hab ⟨h1, h2⟩
    rw [pow_succ, mul_assoc, ibp hP hs, mul_neg, norm_neg]
    exact hC s h1 h2

lemma diff_strip (I : Set ℝ) (hI : IsOpen I) (ψ : ℝ → ℂ) (hP : P I ψ) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x : ℝ, ψ x * Complex.exp (s * x)) {s : ℂ | s.re ∈ I} := by
  intro s0 hs0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI s0.re hs0
  have hδ : 0 < ε / 2 := by positivity
  have hlo : s0.re - ε / 2 ∈ I := hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have hhi : s0.re + ε / 2 ∈ I := hball (by rw [Metric.mem_ball, Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  obtain ⟨g1, hg1⟩ := hP _ hlo
  obtain ⟨g2, hg2⟩ := hP _ hhi
  obtain ⟨g0, hg0⟩ := hP _ hs0
  apply DifferentiableAt.differentiableWithinAt
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x : ℝ => ψ x * Complex.exp (s * x)) volume :=
    fun s => ((continuous_psi hg0).mul (by fun_prop)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := s0)
    (F := fun s x => ψ x * Complex.exp (s * x))
    (F' := fun s x => ψ x * (x * Complex.exp (s * x)))
    (bound := fun x => ‖x‖ * (‖g1 x‖ + ‖g2 x‖))
    (Metric.ball_mem_nhds s0 hδ) (Filter.Eventually.of_forall hmeas) (integrable_of hg0 rfl)
    (((continuous_psi hg0).mul (by fun_prop)).aestronglyMeasurable) ?_ ?_ ?_).2.differentiableAt
  · refine Filter.Eventually.of_forall fun x s hs => ?_
    have hre : |s.re - s0.re| < ε / 2 := by
      have := Complex.abs_re_le_norm (s - s0)
      rw [Metric.mem_ball, dist_eq_norm] at hs
      rw [← Complex.sub_re]; linarith
    rw [abs_lt] at hre
    have hb := norm_le_sum hg1 hg2 (σ := s.re) (by linarith) (by linarith) x
    rw [norm_mul, norm_mul, norm_cexp_mul, Complex.norm_real]
    have hx := norm_nonneg x
    calc ‖ψ x‖ * (‖x‖ * Real.exp (s.re * x)) = ‖x‖ * (‖ψ x‖ * Real.exp (s.re * x)) := by ring
      _ ≤ ‖x‖ * (‖g1 x‖ + ‖g2 x‖) := mul_le_mul_of_nonneg_left hb hx
  · refine ((g1.integrable_pow_mul volume 1).add (g2.integrable_pow_mul volume 1)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, pow_one]; ring
  · refine Filter.Eventually.of_forall fun x s _ => ?_
    have := (((hasDerivAt_id' s).mul_const (x : ℂ)).cexp).const_mul (ψ x)
    exact this.congr_deriv (by ring)

end B1Aux

theorem solution (I : Set ℝ) (hI : IsOpen I) (ψ : ℝ → ℂ)
    (hψ : ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ, g x = (Real.exp (a * x) : ℂ) * ψ x) :
    (∀ s : ℂ, s.re ∈ I → Integrable (fun x : ℝ => ψ x * Complex.exp (s * x))) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ x : ℝ, ψ x * Complex.exp (s * x)) {s : ℂ | s.re ∈ I} ∧
    ∀ a b : ℝ, Set.Icc a b ⊆ I → ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s ^ N * ∫ x : ℝ, ψ x * Complex.exp (s * x)‖ ≤ C := by
  refine ⟨fun s hs => ?_, B1Aux.diff_strip I hI ψ hψ,
    fun a b hab N => B1Aux.strip_bound I N ψ hψ a b hab⟩
  obtain ⟨g, hg⟩ := hψ _ hs
  exact B1Aux.integrable_of hg rfl
