-- Prove2me | solution 1 for NewtonCartan.ng2_equiv_gng
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T18:15:46.111836+00:00
-- url     : https://prove2.me/submissions/f8640033-e9b1-4a30-bee1-25b5e4a72438

import Mathlib
import Definitions.Def_NewtonCartan_defs
import Theorems.Thm_NewtonCartan_geometrization
import Theorems.Thm_NewtonCartan_geom_naturality
import Theorems.Thm_NewtonCartan_exists_recovery_potential
import Theorems.Thm_NewtonCartan_isFlat_of_mapsConn

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


lemma g72w_pd_coord (a b : Fin 4) (x : E) : pd (fun y => y a) b x = if a = b then 1 else 0 := by
  have : (fun y : E => y a) = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a) := rfl
  simp only [pd, this, ContinuousLinearMap.fderiv, ContinuousLinearMap.proj_apply, Pi.single_apply]

lemma g72w_geom_gauge (Γ : Conn) {φ ψ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hχ : ∀ x, χ x = φ x + ψ x) : geomΓ (gaugeΓ Γ ψ) χ = geomΓ Γ φ := by
  have : χ = fun y => φ y + ψ y := funext hχ
  subst this
  funext x a b c
  simp only [geomΓ, gaugeΓ, g71z_grad_add hφ hψ]
  ring

lemma g72w_lap_smooth {Γ : Conn} (hΓ : IsDerivOp Γ) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun x => lap Γ φ x) := by
  unfold lap hess pd2
  refine ContDiff.sum fun a _ => ContDiff.sum fun b _ => contDiff_const.mul ?_
  refine ContDiff.sub (g71z_cd_pd (g71z_cd_pd hφ b) a) ?_
  exact ContDiff.sum fun n _ => (g71z_cd_comp hΓ.1 n a b).mul (g71z_cd_pd hφ n)

theorem solution :
    (∀ Γ φ, IsNG Γ φ → IsGNG (geomΓ Γ φ) ∧ SameTrajectories Γ φ (geomΓ Γ φ)) ∧
    (∀ Γ φ Γ' φ' f ψ, IsNG Γ φ → IsNG Γ' φ' → IsNG2Arrow Γ φ Γ' φ' f ψ →
      IsGNGArrow (geomΓ Γ φ) (geomΓ Γ' φ') f) ∧
    (∀ Γ φ Γ' φ' f, IsNG Γ φ → IsNG Γ' φ' → IsGNGArrow (geomΓ Γ φ) (geomΓ Γ' φ') f →
      ∃! ψ : E → ℝ, IsNG2Arrow Γ φ Γ' φ' f ψ) ∧
    (∀ Γt, IsGNG Γt → ∃ (Γ : Conn) (φ : E → ℝ) (f : E ≃ E), IsNG Γ φ ∧
      IsGNGArrow (geomΓ Γ φ) Γt f ∧ IsGNGArrow Γt (geomΓ Γ φ) f.symm) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ φ hNG
    set ρ : E → ℝ := fun x => lap Γ φ x / (4 * Real.pi)
    have hρ : ContDiff ℝ ∞ ρ := (g72w_lap_smooth hNG.1.1 hNG.2.2).div_const _
    have hP : Poisson Γ φ ρ := by
      intro x; simp only [ρ]; field_simp
    obtain ⟨h1, h2, -, h4⟩ := geometrization Γ φ ρ hNG hρ hP
    exact ⟨⟨h1, ρ, hρ, h4⟩, h2⟩
  · intro Γ φ Γ' φ' f ψ hNG hNG' ⟨hg, ⟨hdf, hpm, hmc⟩, hpush⟩
    refine ⟨hdf, hpm, ?_⟩
    have hψ := hg.1
    have hφ := hNG.2.2
    have hχ : ContDiff ℝ ∞ (fun x => φ x + ψ x) := hφ.add hψ
    have := (geom_naturality (gaugeΓ Γ ψ) Γ' (fun x => φ x + ψ x) φ' f hdf hpm hχ hNG'.2.2 hpush).1 hmc
    rwa [g72w_geom_gauge Γ hφ hψ (fun x => rfl)] at this
  · intro Γ φ Γ' φ' f hNG hNG' ⟨hdf, hpm, hmc⟩
    have hφ := hNG.2.2
    have hφ' := hNG'.2.2
    set ψ : E → ℝ := fun x => φ' (f x) - φ x with hψdef
    have hψ : ContDiff ℝ ∞ ψ := (hφ'.comp hdf.1).sub hφ
    have hpush : ∀ x, φ' (f x) = φ x + ψ x := fun x => by simp [ψ]
    have hχ : ContDiff ℝ ∞ (fun x => φ' (f x)) := hφ'.comp hdf.1
    have hmapsB : MapsConn f (gaugeΓ Γ ψ) Γ' := by
      apply (geom_naturality (gaugeΓ Γ ψ) Γ' (fun x => φ' (f x)) φ' f hdf hpm hχ hφ' (fun x => rfl)).2
      rwa [g72w_geom_gauge Γ hφ hψ hpush]
    have hcl := g71z_classical_gauge hNG.1 hψ
    have hflatB : IsFlat (gaugeΓ Γ ψ) :=
      isFlat_of_mapsConn f hdf _ _ hcl.1 hNG'.1.1 hmapsB hNG'.2.1
    have hgauge : IsGauge Γ ψ := by
      rw [g71z_gauge_iff_N hNG.1 ψ hψ]
      exact (g71z_flat_iff hNG.1 hNG.2.1 hψ).1 hflatB
    refine ⟨ψ, ⟨hgauge, ⟨hdf, hpm, hmapsB⟩, hpush⟩, ?_⟩
    rintro ψ' ⟨-, -, hp'⟩
    funext x; have := hp' x; simp only [ψ]; linarith
  · rintro Γt ⟨hcl, ρ, hρ, hcurv⟩
    obtain ⟨φ, hNG, -⟩ := exists_recovery_potential Γt ρ hcl hρ hcurv
    have hgeom : geomΓ (gaugeΓ Γt φ) φ = Γt := by
      funext x a b c; simp [geomΓ, gaugeΓ]
    have hid : IsGNGArrow Γt Γt (Equiv.refl E) := by
      refine ⟨⟨contDiff_id, contDiff_id⟩, ⟨?_, ?_⟩, ?_⟩
      · intro x b
        simp only [Equiv.refl_apply, g72w_pd_coord]
        simp [Fin.sum_univ_four, tt]
      · intro x a b
        simp only [Equiv.refl_apply, g72w_pd_coord]
        fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_four, hh]
      · intro x a b c
        have h0 : ∀ d : Fin 4, (fun y : E => pd (fun z => (Equiv.refl E) z a) d y) = fun _ => if a = d then 1 else 0 :=
          fun d => funext fun y => by simp only [Equiv.refl_apply]; exact g72w_pd_coord a d y
        simp only [pd2, h0, g71z_pd_const, Equiv.refl_apply, g72w_pd_coord]
        simp [Fin.sum_univ_four]
    refine ⟨gaugeΓ Γt φ, φ, Equiv.refl E, hNG, ?_, ?_⟩
    · rw [hgeom]; exact hid
    · rw [hgeom]; exact hid
