-- Prove2me | solution 1 for NewtonCartan.gauge_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:09:40.128406+00:00
-- url     : https://prove2.me/submissions/9cc191e4-3a59-492b-9f4c-cb624dd62f37

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

lemma g71z_accel_gauge (Γ : Conn) (ψ : E → ℝ) (γ : ℝ → E) (s : ℝ) (a : Fin 4) :
    accel (gaugeΓ Γ ψ) γ s a = accel Γ γ s a - (deriv γ s 0) ^ 2 * gradUp ψ (γ s) a := by
  simp only [accel, gaugeΓ, Fin.sum_univ_four, tt]; simp; ring

lemma g71z_quad (D : Fin 4 → Fin 4 → ℝ) (hD : ∀ b c, D b c = D c b) (k : ℝ)
    (h : ∀ ξ : E, ξ 0 = 1 → ∑ b, ∑ c, D b c * ξ b * ξ c = k) :
    ∀ b c, D b c = tt b * tt c * k := by
  have f : ∀ y1 y2 y3 : ℝ, D 0 0 + D 0 1 * y1 + D 0 2 * y2 + D 0 3 * y3 +
      (D 1 0 * y1 + D 1 1 * y1 * y1 + D 1 2 * y1 * y2 + D 1 3 * y1 * y3) +
      (D 2 0 * y2 + D 2 1 * y2 * y1 + D 2 2 * y2 * y2 + D 2 3 * y2 * y3) +
      (D 3 0 * y3 + D 3 1 * y3 * y1 + D 3 2 * y3 * y2 + D 3 3 * y3 * y3) = k := by
    intro y1 y2 y3
    have := h ![1, y1, y2, y3] rfl
    simpa [Fin.sum_univ_four] using this
  have a0 := f 0 0 0
  have a1 := f 1 0 0; have a2 := f (-1) 0 0
  have a3 := f 0 1 0; have a4 := f 0 (-1) 0
  have a5 := f 0 0 1; have a6 := f 0 0 (-1)
  have a7 := f 1 1 0; have a8 := f 1 0 1; have a9 := f 0 1 1
  have s01 := hD 0 1; have s02 := hD 0 2; have s03 := hD 0 3
  have s12 := hD 1 2; have s13 := hD 1 3; have s23 := hD 2 3
  intro b c
  fin_cases b <;> fin_cases c <;> simp [tt] <;> linarith

lemma g71z_boot {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : W → W}
    (hF : ContDiff ℝ ∞ F) {α : ℝ → W} {s : Set ℝ} (hs : IsOpen s)
    (hα : ∀ t ∈ s, HasDerivAt α (F (α t)) t) : ContDiffOn ℝ ∞ α s := by
  rw [contDiffOn_infty]; intro m
  induction m with
  | zero => exact contDiffOn_zero.2 (fun t ht => (hα t ht).continuousAt.continuousWithinAt)
  | succ m ih =>
    rw [show ((m+1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun t ht => (hα t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h1 : ContDiffOn ℝ m (F ∘ α) s :=
      (hF.of_le (by exact_mod_cast le_top)).comp_contDiffOn ih
    exact h1.congr (fun t ht => (hα t ht).deriv)

lemma g71z_geod {Γt : Conn} (hΓt : IsClassical Γt) (x ξ : E) (hξ : ξ 0 = 1) :
    ∃ γ : ℝ → E, ∃ ε > (0:ℝ), IsTimelikeOn γ (-ε) ε ∧ IsGeodesicOn Γt γ (-ε) ε ∧
      γ 0 = x ∧ deriv γ 0 = ξ := by
  let F : E × E → E × E := fun p => (p.2, fun a => -∑ b, ∑ c, Γt p.1 a b c * p.2 b * p.2 c)
  have hF : ContDiff ℝ ∞ F := by
    refine contDiff_snd.prodMk (contDiff_pi.2 fun a => ?_)
    refine ContDiff.neg (ContDiff.sum fun b _ => ContDiff.sum fun c _ => ?_)
    exact (((g71z_cd_comp hΓt.1.1 a b c).comp contDiff_fst).mul
      ((contDiff_apply ℝ ℝ b).comp contDiff_snd)).mul ((contDiff_apply ℝ ℝ c).comp contDiff_snd)
  obtain ⟨α, hα0, ε, hε, hα⟩ :=
    ((hF.contDiffAt (x := (x, ξ))).of_le (by simp)).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  simp only [zero_sub, zero_add] at hα
  let γ : ℝ → E := fun t => (α t).1
  let v : ℝ → E := fun t => (α t).2
  have hγ : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt γ (v t) t := fun t ht => by
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht)
    simpa [Function.comp_def, F] using this
  have hv : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt v (F (α t)).2 t := fun t ht => by
    have := (hasFDerivAt_snd (𝕜 := ℝ) (p := α t)).comp_hasDerivAt t (hα t ht)
    simpa [Function.comp_def] using this
  have hdγ : ∀ t ∈ Set.Ioo (-ε) ε, deriv γ =ᶠ[nhds t] v := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hγ s hs).deriv
  have h0mem : (0:ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  -- the time component of the velocity is constant
  have hv0 : ∀ t ∈ Set.Ioo (-ε) ε, v t 0 = 1 := by
    have hd0 : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun t => v t 0) 0 t := by
      intro t ht
      have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).hasFDerivAt
        (x := v t)).comp_hasDerivAt t (hv t ht)
      simp only [Function.comp_def, ContinuousLinearMap.proj_apply] at this
      have e : (F (α t)).2 0 = 0 := by
        simp only [F, g71z_compat0 hΓt.2, zero_mul, Finset.sum_const_zero, neg_zero]
      rw [e] at this; exact this
    intro t ht
    have := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun s hs => (hd0 s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd0 s hs).deriv) ht h0mem
    rw [this]; simp only [v, hα0, hξ]
  refine ⟨γ, ε, hε, ⟨by linarith, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact ((contDiff_fst (𝕜 := ℝ) (E := E) (F := E)).comp_contDiffOn
      (g71z_boot hF isOpen_Ioo hα))
  · intro s hs; rw [(hγ s hs).deriv]; exact hv0 s hs
  · intro s hs a
    simp only [accel]
    rw [(hdγ s hs).deriv_eq, (hv s hs).deriv, (hγ s hs).deriv]
    simp [F, γ, v]
  · simp [γ, hα0]
  · rw [(hγ 0 h0mem).deriv]; simp [v, hα0]

theorem solution (Γt Γ Γ' : Conn) (φ φ' ρ : E → ℝ) (hΓt : IsClassical Γt)
    (hNG : IsNG Γ φ) (hT : SameTrajectories Γ φ Γt) (hP : Poisson Γ φ ρ) :
    (IsNG Γ' φ' ∧ SameTrajectories Γ' φ' Γt ∧ Poisson Γ' φ' ρ) ↔
      (IsGauge Γ (fun x => φ' x - φ x) ∧ Γ' = gaugeΓ Γ (fun x => φ' x - φ x)) := by
  set ψ : E → ℝ := fun x => φ' x - φ x with hψdef
  have hφ'eq : φ' = fun y => φ y + ψ y := funext fun y => by simp [ψ]
  have hΓ := hNG.1
  constructor
  · rintro ⟨hNG', hT', hP'⟩
    have hψ : ContDiff ℝ ∞ ψ := hNG'.2.2.sub hNG.2.2
    have hgrad : ∀ x a, gradUp φ' x a = gradUp φ x a + gradUp ψ x a := by
      intro x a; rw [hφ'eq]; exact g71z_grad_add hNG.2.2 hψ x a
    have hΓ'eq : Γ' = gaugeΓ Γ ψ := by
      funext x a b c
      have key := g71z_quad (fun b c => Γ' x a b c - Γ x a b c)
        (fun b c => by rw [hNG'.1.1.2 x a b c, hΓ.1.2 x a b c])
        (-gradUp ψ x a) (fun ξ hξ => by
          obtain ⟨γ, ε, hε, hγt, hγg, hγ0, hγd⟩ := g71z_geod hΓt x ξ hξ
          have h0 : (0:ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
          have n1 := (hT γ _ _ hγt).1 hγg 0 h0 a
          have n2 := (hT' γ _ _ hγt).1 hγg 0 h0 a
          simp only [accel, hγ0, hγd] at n1 n2
          rw [hgrad] at n2
          have : ∑ b, ∑ c, (Γ' x a b c - Γ x a b c) * ξ b * ξ c =
              (∑ b, ∑ c, Γ' x a b c * ξ b * ξ c) - ∑ b, ∑ c, Γ x a b c * ξ b * ξ c := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun c _ => by ring)
          rw [this]; linarith) b c
      simp only [gaugeΓ]
      linarith
    refine ⟨?_, hΓ'eq⟩
    rw [g71z_gauge_iff_N hΓ ψ hψ, ← g71z_flat_iff hΓ hNG.2.1 hψ, ← hΓ'eq]
    exact hNG'.2.1
  · rintro ⟨hg, hΓ'eq⟩
    have hψ : ContDiff ℝ ∞ ψ := hg.1
    have hφ' : ContDiff ℝ ∞ φ' := by rw [hφ'eq]; exact hNG.2.2.add hψ
    have hgrad : ∀ x a, gradUp φ' x a = gradUp φ x a + gradUp ψ x a := by
      intro x a; rw [hφ'eq]; exact g71z_grad_add hNG.2.2 hψ x a
    rw [hΓ'eq]
    refine ⟨⟨g71z_classical_gauge hΓ hψ, (g71z_flat_iff hΓ hNG.2.1 hψ).2
      ((g71z_gauge_iff_N hΓ ψ hψ).1 hg), hφ'⟩, ?_, ?_⟩
    · intro γ s₀ s₁ hγ
      rw [hT γ s₀ s₁ hγ]
      unfold IsNewtonianOn
      refine forall_congr' fun s => forall_congr' fun hs => forall_congr' fun a => ?_
      rw [g71z_accel_gauge, hγ.2.2 s hs, hgrad]
      constructor <;> intro h <;> linarith
    · intro x
      rw [g71z_lap_gauge, hφ'eq]
      have : lap Γ (fun y => φ y + ψ y) x = lap Γ φ x + lap Γ ψ x := by
        simp only [lap, g71z_hess_add Γ hNG.2.2 hψ, mul_add, Finset.sum_add_distrib]
      rw [this, g71z_lap_gauge_zero hg, hP x, add_zero]
