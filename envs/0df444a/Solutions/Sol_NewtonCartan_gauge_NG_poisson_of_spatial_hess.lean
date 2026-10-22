-- Prove2me | solution 1 for NewtonCartan.gauge_NG_poisson_of_spatial_hess
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T18:02:46.660904+00:00
-- url     : https://prove2.me/submissions/092b739e-dbc5-4527-b59b-8e6163ec9ce6

import Mathlib
import Definitions.Def_NewtonCartan_defs

open scoped ContDiff
open NewtonCartan

lemma g71z_pd_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (b : Fin 4) : pd (fun y => f y - g y) b x = pd f b x - pd g b x := by
  simp only [pd]; rw [fderiv_fun_sub hf hg]; rfl

lemma g71z_pd_add {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (b : Fin 4) : pd (fun y => f y + g y) b x = pd f b x + pd g b x := by
  simp only [pd]; rw [fderiv_fun_add hf hg]; rfl

lemma g71z_pd_const_mul {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (c : ℝ)
    (b : Fin 4) : pd (fun y => c * f y) b x = c * pd f b x := by
  simp only [pd]; rw [fderiv_const_mul hf]; rfl

lemma g71z_pd_const (c : ℝ) (b : Fin 4) (x : E) : pd (fun _ => c) b x = 0 := by
  simp [pd]

lemma g71z_cd_pd {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (n : Fin 4) : ContDiff ℝ ∞ (pd φ n) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  exact h1.clm_apply contDiff_const

lemma g71z_cd_grad {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (a : Fin 4) :
    ContDiff ℝ ∞ (fun y => gradUp φ y a) := by
  unfold gradUp
  exact ContDiff.sum (fun n _ => contDiff_const.mul (g71z_cd_pd hφ n))

lemma g71z_cd_comp {Γ : Conn} (hΓ : ContDiff ℝ ∞ Γ) (a b c : Fin 4) :
    ContDiff ℝ ∞ (fun y => Γ y a b c) := by
  have h1 : ContDiff ℝ ∞ (fun y => Γ y a) := (contDiff_pi.1 hΓ) a
  have h2 : ContDiff ℝ ∞ (fun y => Γ y a b) := (contDiff_pi.1 h1) b
  exact (contDiff_pi.1 h2) c

lemma g71z_grad0 (φ : E → ℝ) (x : E) : gradUp φ x 0 = 0 := by
  simp [gradUp, hh]

lemma g71z_grad_sp (φ : E → ℝ) (x : E) (a : Fin 4) (ha : a ≠ 0) : gradUp φ x a = pd φ a x := by
  simp only [gradUp, hh]
  rw [Finset.sum_eq_single a]
  · simp [ha]
  · intro m _ hm; simp [Ne.symm hm]
  · simp

lemma g71z_grad_add {φ ψ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (x : E) (a : Fin 4) :
    gradUp (fun y => φ y + ψ y) x a = gradUp φ x a + gradUp ψ x a := by
  simp only [gradUp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [g71z_pd_add (hφ.differentiable (by simp) x) (hψ.differentiable (by simp) x)]; ring

lemma g71z_tt0 : tt 0 = 1 := by simp [tt]

lemma g71z_compat0 {Γ : Conn} (hc : Compatible Γ) (x : E) (b c : Fin 4) : Γ x 0 b c = 0 := by
  have := hc.1 x b c
  simpa [Fin.sum_univ_four, tt] using this

/-- the covariant derivative of the gradient -/
noncomputable def g71z_N (Γ : Conn) (ψ : E → ℝ) (x : E) (c a : Fin 4) : ℝ :=
  pd (fun y => gradUp ψ y a) c x + ∑ e, Γ x a c e * gradUp ψ x e

lemma g71z_riem_gauge {Γ : Conn} (hΓ : IsClassical Γ) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (x : E) (a b c d : Fin 4) :
    riem (gaugeΓ Γ ψ) x a b c d =
      riem Γ x a b c d - tt b * (tt c * g71z_N Γ ψ x d a - tt d * g71z_N Γ ψ x c a) := by
  have hd : ∀ p q r : Fin 4, DifferentiableAt ℝ (fun y => Γ y p q r) x := fun p q r =>
    (g71z_cd_comp hΓ.1.1 p q r).differentiable (by simp) x
  have hg : ∀ p : Fin 4, DifferentiableAt ℝ (fun y => gradUp ψ y p) x := fun p =>
    (g71z_cd_grad hψ p).differentiable (by simp) x
  have e1 : ∀ p q r s : Fin 4, pd (fun y => gaugeΓ Γ ψ y p q r) s x =
      pd (fun y => Γ y p q r) s x - tt q * tt r * pd (fun y => gradUp ψ y p) s x := by
    intro p q r s
    simp only [gaugeΓ]
    rw [g71z_pd_sub (hd p q r) ((hg p).const_mul _), g71z_pd_const_mul (hg p)]
  simp only [riem, e1, g71z_N]
  simp only [gaugeΓ, Fin.sum_univ_four, g71z_grad0, g71z_compat0 hΓ.2, tt]
  simp only [Fin.isValue, ↓reduceIte, mul_zero, sub_zero, zero_mul, mul_one, one_ne_zero,
    Fin.reduceEq]
  ring

lemma g71z_compat_sp {Γ : Conn} (hc : Compatible Γ) (x : E) (a b e : Fin 4) (hb : b ≠ 0)
    (he : e ≠ 0) : Γ x b a e + Γ x e a b = 0 := by
  have := hc.2 x a b e
  fin_cases b <;> fin_cases e <;> simp_all [Fin.sum_univ_four, hh] <;> linarith

lemma g71z_hess_eq_N {Γ : Conn} (hΓ : IsClassical Γ) (ψ : E → ℝ) (x : E) (a b : Fin 4)
    (hb : b ≠ 0) : hess Γ ψ x a b = g71z_N Γ ψ x a b := by
  have hfun : (fun y => gradUp ψ y b) = fun y => pd ψ b y := funext fun y => g71z_grad_sp ψ y b hb
  simp only [hess, g71z_N, hfun, pd2]
  have hs : ∑ e, Γ x b a e * gradUp ψ x e = -∑ n, Γ x n a b * pd ψ n x := by
    simp only [Fin.sum_univ_four, g71z_grad0, g71z_compat0 hΓ.2]
    rw [g71z_grad_sp ψ x 1 (by decide), g71z_grad_sp ψ x 2 (by decide),
      g71z_grad_sp ψ x 3 (by decide)]
    have h1 := g71z_compat_sp hΓ.2 x a b 1 hb (by decide)
    have h2 := g71z_compat_sp hΓ.2 x a b 2 hb (by decide)
    have h3 := g71z_compat_sp hΓ.2 x a b 3 hb (by decide)
    linear_combination (pd ψ 1 x) * h1 + (pd ψ 2 x) * h2 + (pd ψ 3 x) * h3
  rw [hs]; ring

lemma g71z_hh_sum (a b : Fin 4) (f : Fin 4 → Fin 4 → ℝ) :
    ∑ m, ∑ n, hh a m * hh b n * f m n = if a ≠ 0 ∧ b ≠ 0 then f a b else 0 := by
  fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_four, hh]

lemma g71z_N_i0 {Γ : Conn} (hΓ : IsClassical Γ) (ψ : E → ℝ) (x : E) (i : Fin 4) :
    g71z_N Γ ψ x i 0 = 0 := by
  have : (fun y => gradUp ψ y 0) = fun _ => (0:ℝ) := funext fun y => g71z_grad0 ψ y
  simp only [g71z_N, this, g71z_pd_const, g71z_compat0 hΓ.2, zero_mul, Finset.sum_const_zero,
    add_zero]

lemma g71z_gauge_iff_N {Γ : Conn} (hΓ : IsClassical Γ) (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    IsGauge Γ ψ ↔ ∀ x, ∀ i : Fin 4, i ≠ 0 → ∀ a, g71z_N Γ ψ x i a = 0 := by
  constructor
  · intro h x i hi a
    by_cases ha : a = 0
    · rw [ha]; exact g71z_N_i0 hΓ ψ x i
    · have := h.2 x i a
      rw [g71z_hh_sum, if_pos ⟨hi, ha⟩, g71z_hess_eq_N hΓ ψ x i a ha] at this
      exact this
  · intro h
    refine ⟨hψ, fun x a b => ?_⟩
    rw [g71z_hh_sum]
    split_ifs with hab
    · rw [g71z_hess_eq_N hΓ ψ x a b hab.2]; exact h x a hab.1 b
    · rfl

lemma g71z_flat_iff {Γ : Conn} (hΓ : IsClassical Γ) (hfl : IsFlat Γ) {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) :
    IsFlat (gaugeΓ Γ ψ) ↔ ∀ x, ∀ i : Fin 4, i ≠ 0 → ∀ a, g71z_N Γ ψ x i a = 0 := by
  constructor
  · intro h x i hi a
    have := h x a 0 0 i
    rw [g71z_riem_gauge hΓ hψ, hfl] at this
    have hti : tt i = 0 := by simp [tt, hi]
    rw [hti, g71z_tt0] at this
    linarith
  · intro h x a b c d
    rw [g71z_riem_gauge hΓ hψ, hfl]
    by_cases hc : c = 0 <;> by_cases hd : d = 0
    · subst hc; subst hd; ring
    · subst hc; rw [h x d hd a]; simp [tt, hd]
    · subst hd; rw [h x c hc a]; simp [tt, hc]
    · simp [tt, hc, hd]

lemma g71z_classical_gauge {Γ : Conn} (hΓ : IsClassical Γ) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    IsClassical (gaugeΓ Γ ψ) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold gaugeΓ
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => contDiff_pi.2 fun c => ?_
    exact (g71z_cd_comp hΓ.1.1 a b c).sub (contDiff_const.mul (g71z_cd_grad hψ a))
  · intro x a b c; simp only [gaugeΓ]; rw [hΓ.1.2 x a b c]; ring
  · intro x b c
    have := hΓ.2.1 x b c
    simp only [gaugeΓ, Fin.sum_univ_four, g71z_grad0] at this ⊢
    simp only [tt] at this ⊢; simp at this ⊢; linarith
  · intro x a b c
    have := hΓ.2.2 x a b c
    simp only [gaugeΓ, Fin.sum_univ_four] at this ⊢
    simp only [tt, hh] at this ⊢; simp at this ⊢; linarith

lemma g71z_lap_gauge (Γ : Conn) (ψ φ : E → ℝ) (x : E) : lap (gaugeΓ Γ ψ) φ x = lap Γ φ x := by
  simp only [lap, hess, gaugeΓ, Fin.sum_univ_four, hh, tt]; simp

lemma g71z_hess_add (Γ : Conn) {φ ψ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (x : E)
    (a b : Fin 4) : hess Γ (fun y => φ y + ψ y) x a b = hess Γ φ x a b + hess Γ ψ x a b := by
  have hfun : (fun y => pd (fun y => φ y + ψ y) b y) = fun y => pd φ b y + pd ψ b y :=
    funext fun y => g71z_pd_add (hφ.differentiable (by simp) y) (hψ.differentiable (by simp) y) b
  simp only [hess, pd2, hfun]
  rw [g71z_pd_add ((g71z_cd_pd hφ b).differentiable (by simp) x)
    ((g71z_cd_pd hψ b).differentiable (by simp) x)]
  have : ∀ n, pd (fun y => φ y + ψ y) n x = pd φ n x + pd ψ n x := fun n =>
    g71z_pd_add (hφ.differentiable (by simp) x) (hψ.differentiable (by simp) x) n
  simp only [this, mul_add, Finset.sum_add_distrib]; ring

lemma g71z_lap_gauge_zero {Γ : Conn} {ψ : E → ℝ} (h : IsGauge Γ ψ) (x : E) : lap Γ ψ x = 0 := by
  have h1 := h.2 x 1 1; have h2 := h.2 x 2 2; have h3 := h.2 x 3 3
  rw [g71z_hh_sum, if_pos ⟨by decide, by decide⟩] at h1 h2 h3
  simp only [lap, Fin.sum_univ_four, hh]; simp [h1, h2, h3]


lemma g72n_riem0 {Γ : Conn} (hΓ : IsClassical Γ) (x : E) (b c d : Fin 4) : riem Γ x 0 b c d = 0 := by
  have h0 : ∀ q r : Fin 4, (fun y => Γ y 0 q r) = fun _ => (0:ℝ) :=
    fun q r => funext fun y => g71z_compat0 hΓ.2 y q r
  simp only [riem, h0, g71z_pd_const, g71z_compat0 hΓ.2, zero_mul, sub_zero, sub_self,
    Finset.sum_const_zero, add_zero]

lemma g72n_spatial {Γ : Conn} (hΓ : IsClassical Γ) (x : E) (i j k : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0)
    (hk : k ≠ 0) : Γ x i j k = 0 := by
  have s := hΓ.1.2 x
  have c1 := g71z_compat_sp hΓ.2 x j i k hi hk
  have c3 := g71z_compat_sp hΓ.2 x i k j hk hj
  have c5 := g71z_compat_sp hΓ.2 x k j i hj hi
  have s2 := s k j i
  have s4 := s j i k
  have s6 := s i k j
  linarith

lemma g72n_key {Γt : Conn} (hΓt : IsClassical Γt) {φ : E → ℝ}
    (hhess : ∀ x i j, i ≠ 0 → j ≠ 0 → pd (fun y => gradUp φ y i) j x = riem Γt x i 0 0 j)
    (x : E) (d a : Fin 4) (hd : d ≠ 0) : g71z_N Γt φ x d a = riem Γt x a 0 0 d := by
  by_cases ha : a = 0
  · subst ha; rw [g71z_N_i0 hΓt, g72n_riem0 hΓt]
  · simp only [g71z_N]
    rw [hhess x a d ha hd]
    have : ∑ e, Γt x a d e * gradUp φ x e = 0 := by
      apply Finset.sum_eq_zero; intro e _
      by_cases he : e = 0
      · subst he; rw [g71z_grad0]; ring
      · rw [g72n_spatial hΓt x a d e ha hd he]; ring
    rw [this, add_zero]

theorem solution (Γt : Conn) (ρ : E → ℝ) (φ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ)
    (hφ : ContDiff ℝ ∞ φ)
    (hform : ∀ x a b c d,
      riem Γt x a b c d =
        tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c))
    (hhess : ∀ x i j, i ≠ 0 → j ≠ 0 →
      pd (fun y => gradUp φ y i) j x = riem Γt x i 0 0 j) :
    IsNG (gaugeΓ Γt φ) φ ∧ Poisson (gaugeΓ Γt φ) φ ρ := by
  have hN := g72n_key hΓt hhess
  refine ⟨⟨g71z_classical_gauge hΓt hφ, ?_, hφ⟩, ?_⟩
  · intro x a b c d
    rw [g71z_riem_gauge hΓt hφ, hform]
    by_cases hc : c = 0 <;> by_cases hd : d = 0
    · subst hc; subst hd; ring
    · subst hc; rw [hN x d a hd]; simp [tt, hd]
    · subst hd; rw [hN x c a hc]; simp [tt, hc]
    · simp [tt, hc, hd]
  · intro x
    rw [g71z_lap_gauge]
    have hl : lap Γt φ x = ∑ i ∈ ({1, 2, 3} : Finset (Fin 4)), hess Γt φ x i i := by
      simp [lap, Fin.sum_univ_four, hh]; ring
    rw [hl]
    have hric := hcurv.1 x 0 0
    simp only [ricci, Fin.sum_univ_four, g72n_riem0 hΓt, g71z_tt0] at hric
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [g71z_hess_eq_N hΓt φ x 1 1 (by decide), g71z_hess_eq_N hΓt φ x 2 2 (by decide),
      g71z_hess_eq_N hΓt φ x 3 3 (by decide), hN x 1 1 (by decide), hN x 2 2 (by decide),
      hN x 3 3 (by decide)]
    linarith
