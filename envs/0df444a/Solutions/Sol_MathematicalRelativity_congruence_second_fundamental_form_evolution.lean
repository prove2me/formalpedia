-- Prove2me | solution 1 for MathematicalRelativity.congruence_second_fundamental_form_evolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:31:34.403554+00:00
-- url     : https://prove2.me/submissions/508487b2-36ba-4292-ad8a-5929eca7ea19

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

set_option autoImplicit false

open scoped ContDiff

open MathematicalRelativity

theorem a23_da {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (x : Pt) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)).differentiableAt

theorem a23_pd_sm {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) : ContDiff ℝ ∞ (pd f i) := by
  unfold pd
  exact ((contDiff_infty_iff_fderiv.1 hf).2).clm_apply contDiff_const

theorem a23_pd_sub {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y - g y) i x = pd f i x - pd g i x := by
  simp only [pd, fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

theorem a23_pd_mul {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  simp only [pd, fderiv_fun_mul hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem a23_pd_sum {A : Fin 4 → Pt → ℝ} {x : Pt} (h : ∀ i, DifferentiableAt ℝ (A i) x)
    (k : Fin 4) : pd (fun y => ∑ i, A i y) k x = ∑ i, pd (A i) k x := by
  simp only [pd, fderiv_fun_sum (fun i _ => h i), ContinuousLinearMap.sum_apply]

theorem a23_clairaut {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (x : Pt) (i j : Fin 4) :
    pd (pd f i) j x = pd (pd f j) i x := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_infty_iff_fderiv.1 hf).2).differentiable (by simp)
  have key : ∀ k l : Fin 4, pd (pd f k) l x
      = fderiv ℝ (fderiv ℝ f) x (Pi.single l 1) (Pi.single k 1) := by
    intro k l
    have h := (ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1:ℝ) : Pt)).hasFDerivAt.comp x
      (hd x).hasFDerivAt
    show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single k 1)) x (Pi.single l 1) = _
    rw [show (fun y => fderiv ℝ f y (Pi.single k 1))
        = (ContinuousLinearMap.apply ℝ ℝ (Pi.single k (1:ℝ) : Pt)) ∘ fderiv ℝ f from rfl,
      h.fderiv]
    rfl
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [key, key]
  exact hs _ _

theorem a23_det_ne (m : Spacetime) (y : Pt) : (m.mat y).det ≠ 0 := by
  obtain ⟨P, _, hPe⟩ := m.lorentz y
  have h := congrArg Matrix.det hPe
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  intro h0
  rw [show Matrix.of (m.g y) = m.mat y from rfl, h0] at h
  simp [eta, Matrix.det_diagonal] at h

theorem a23_det_sm {f : Pt → Matrix (Fin 4) (Fin 4) ℝ}
    (hf : ∀ i j, ContDiff ℝ ∞ (fun x => f x i j)) :
    ContDiff ℝ ∞ (fun x => (f x).det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem a23_ginv_sm (m : Spacetime) (i j : Fin 4) : ContDiff ℝ ∞ (fun y => m.ginv y i j) := by
  have hent : ∀ k l, ContDiff ℝ ∞ (fun y => m.mat y k l) := fun k l => m.smooth k l
  have e : (fun y => m.ginv y i j)
      = fun y => ((m.mat y).det)⁻¹ * (m.mat y).adjugate i j := by
    funext y; simp [Spacetime.ginv, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  refine ContDiff.mul ((a23_det_sm hent).inv (a23_det_ne m)) ?_
  simp only [Matrix.adjugate_apply]
  apply a23_det_sm
  intro k l
  by_cases h : k = j
  · subst h; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne h]; exact hent k l

theorem a23_chr_sm (m : Spacetime) (a b c : Fin 4) : ContDiff ℝ ∞ (m.christoffel a b c) := by
  have h1 := a23_ginv_sm m
  have h2 : ∀ i j k, ContDiff ℝ ∞ (pd (fun y => m.g y i j) k) :=
    fun i j k => a23_pd_sm (m.smooth i j) k
  unfold Spacetime.christoffel
  fun_prop

theorem a23_Xl_sm (m : Spacetime) (K : Congruence m) (c : Fin 4) :
    ContDiff ℝ ∞ (fun y => m.lower y (K.X y) c) := by
  unfold Spacetime.lower
  have := m.smooth
  have := K.smooth
  fun_prop

theorem a23_B_sm (m : Spacetime) (K : Congruence m) (u v : Fin 4) :
    ContDiff ℝ ∞ (K.B u v) := by
  have h1 := a23_Xl_sm m K
  have h2 := a23_chr_sm m
  have h3 : ∀ c k, ContDiff ℝ ∞ (pd (fun y => m.lower y (K.X y) c) k) :=
    fun c k => a23_pd_sm (h1 c) k
  unfold Congruence.B Spacetime.covCov
  fun_prop
theorem a23_L6 (g : Fin 4 → Fin 4 → ℝ) (X Xl : Fin 4 → ℝ) (R : Fin 4 → Fin 4 → ℝ)
    (h6 : ∀ e, ∑ ga, g ga e * X ga = Xl e) :
    ∑ ga, ∑ al, (∑ e, g ga e * R e al) * X ga * X al = ∑ al, ∑ e, Xl e * R e al * X al := by
  simp only [← h6]
  simp only [Fin.sum_univ_four]
  ring

theorem a23_core
    (X Xl : Fin 4 → ℝ) (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (dG : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (B : Fin 4 → Fin 4 → ℝ) (dB : Fin 4 → Fin 4 → Fin 4 → ℝ) (dX dXl : Fin 4 → Fin 4 → ℝ)
    (ddXl : Fin 4 → Fin 4 → Fin 4 → ℝ) (gi g : Fin 4 → Fin 4 → ℝ) (u v : Fin 4)
    (hGs : ∀ b a, G b a v = G b v a)
    (h1 : ∀ c a, dXl c a = B c a + ∑ d, G d a c * Xl d)
    (h2 : ∀ a, dB u v a = ddXl u v a - ∑ c, (dG c v u a * Xl c + G c v u * dXl c a))
    (h2' : ∀ a, dB u a v = ddXl u a v - ∑ c, (dG c a u v * Xl c + G c a u * dXl c v))
    (hsym : ∀ a, ddXl u v a = ddXl u a v)
    (h3 : ∀ c, ∑ b, X b * B c b = 0)
    (h4 : ∑ b, (dX b v * B u b + X b * dB u b v) = 0)
    (h5 : ∀ b, ∑ e, gi b e * B e v = dX b v + ∑ c, G b v c * X c)
    (h6 : ∀ e, ∑ ga, g ga e * X ga = Xl e) :
    ∑ a, X a * (dB u v a - ∑ b, G b a u * B b v - ∑ b, G b a v * B u b)
      = -(∑ al, ∑ be, B u al * gi al be * B be v)
        - ∑ ga, ∑ al, (∑ e, g ga e * (dG e v u al - dG e al u v
            + ∑ f, (G e al f * G f v u - G e v f * G f al u))) * X ga * X al := by
  rw [a23_L6 g X Xl _ h6]
  have hBgB : ∑ al, ∑ be, B u al * gi al be * B be v
      = ∑ al, B u al * (dX al v + ∑ c, G al v c * X c) := by
    refine Finset.sum_congr rfl fun al _ => ?_
    rw [← h5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun be _ => ?_
    ring
  rw [hBgB]
  have hdB : ∀ a, dB u v a = dB u a v
      - ∑ c, (dG c v u a * Xl c + G c v u * dXl c a)
      + ∑ c, (dG c a u v * Xl c + G c a u * dXl c v) := by
    intro a; rw [h2, h2', hsym]; ring
  simp only [hdB, h1, hGs]
  have h3' := h3
  simp only [Fin.sum_univ_four] at h3' h4 ⊢
  linear_combination h4
    - G 0 v u * h3' 0 - G 1 v u * h3' 1 - G 2 v u * h3' 2 - G 3 v u * h3' 3

theorem a23_mul_ginv (m : Spacetime) (y : Pt) (u e : Fin 4) :
    ∑ d, m.g y u d * m.ginv y d e = if u = e then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv (m.mat y)
    (isUnit_iff_ne_zero.2 (a23_det_ne m y))) u) e
  simpa [Matrix.mul_apply, Matrix.one_apply, Spacetime.mat, Spacetime.ginv] using h

theorem a23_ginv_mul (m : Spacetime) (y : Pt) (b c : Fin 4) :
    ∑ e, m.ginv y b e * m.g y e c = if b = c then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (m.mat y)
    (isUnit_iff_ne_zero.2 (a23_det_ne m y))) b) c
  simpa [Matrix.mul_apply, Matrix.one_apply, Spacetime.mat, Spacetime.ginv] using h

theorem a23_lowchr (m : Spacetime) (y : Pt) (u b j : Fin 4) :
    ∑ d, m.g y u d * m.christoffel d b j y
      = 1/2 * (pd (fun z => m.g z u j) b y + pd (fun z => m.g z u b) j y
          - pd (fun z => m.g z b j) u y) := by
  have key : ∀ T : Fin 4 → ℝ,
      ∑ d, m.g y u d * ((1/2 : ℝ) * ∑ e, m.ginv y d e * T e) = (1/2) * T u := by
    intro T
    have h : ∑ d, m.g y u d * ((1/2 : ℝ) * ∑ e, m.ginv y d e * T e)
        = (1/2) * ∑ e, (∑ d, m.g y u d * m.ginv y d e) * T e := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h]
    simp [a23_mul_ginv]
  unfold Spacetime.christoffel
  exact key (fun e => pd (fun z => m.g z e j) b y + pd (fun z => m.g z e b) j y
    - pd (fun z => m.g z b j) e y)

theorem a23_dg (m : Spacetime) (y : Pt) (u j b : Fin 4) :
    pd (fun z => m.g z u j) b y
      = ∑ d, m.g y u d * m.christoffel d b j y + ∑ d, m.g y j d * m.christoffel d b u y := by
  rw [a23_lowchr, a23_lowchr]
  have e1 : (fun z => m.g z j u) = (fun z => m.g z u j) := funext fun z => m.symm z j u
  have e2 : (fun z => m.g z j b) = (fun z => m.g z b j) := funext fun z => m.symm z j b
  have e3 : (fun z => m.g z b u) = (fun z => m.g z u b) := funext fun z => m.symm z b u
  rw [e1, e2, e3]
  ring

theorem a23_MC (m : Spacetime) (K : Congruence m) (y : Pt) (u b : Fin 4) :
    K.B u b y = ∑ c, m.g y u c * m.covVec K.X c b y := by
  have hXl : (fun z => m.lower z (K.X z) u) = fun z => ∑ j, m.g z u j * K.X z j := rfl
  have hpd : pd (fun z => ∑ j, m.g z u j * K.X z j) b y
      = ∑ j, (pd (fun z => m.g z u j) b y * K.X y j + m.g y u j * pd (fun z => K.X z j) b y) := by
    rw [a23_pd_sum (fun j => ((m.smooth u j).mul (K.smooth j)).differentiable (by simp) y)]
    exact Finset.sum_congr rfl fun j _ =>
      a23_pd_mul (a23_da (m.smooth u j) y) (a23_da (K.smooth j) y) b
  unfold Congruence.B Spacetime.covCov Spacetime.covVec
  rw [hXl, hpd]
  simp only [a23_dg m y, Spacetime.lower]
  simp only [Fin.sum_univ_four]
  simp only [m.symm y 1 0, m.symm y 2 0, m.symm y 3 0, m.symm y 2 1, m.symm y 3 1,
    m.symm y 3 2]
  ring

theorem a23_h3 (m : Spacetime) (K : Congruence m) (y : Pt) (c : Fin 4) :
    ∑ b, K.X y b * K.B c b y = 0 := by
  calc ∑ b, K.X y b * K.B c b y
      = ∑ c', m.g y c c' * ∑ b, m.covVec K.X c' b y * K.X y b := by
        simp only [a23_MC m K y, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by simp [K.geodesic y]

theorem a23_h5 (m : Spacetime) (K : Congruence m) (x : Pt) (b v : Fin 4) :
    ∑ e, m.ginv x b e * K.B e v x
      = pd (fun y => K.X y b) v x + ∑ c, m.christoffel b v c x * K.X x c := by
  calc ∑ e, m.ginv x b e * K.B e v x
      = ∑ c, (∑ e, m.ginv x b e * m.g x e c) * m.covVec K.X c v x := by
        simp only [a23_MC m K x, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ = m.covVec K.X b v x := by simp [a23_ginv_mul]
    _ = _ := rfl

theorem a23_h2 (m : Spacetime) (K : Congruence m) (x : Pt) (u v a : Fin 4) :
    pd (K.B u v) a x = pd (pd (fun y => m.lower y (K.X y) u) v) a x
      - ∑ c, (pd (m.christoffel c v u) a x * m.lower x (K.X x) c
          + m.christoffel c v u x * pd (fun y => m.lower y (K.X y) c) a x) := by
  have hB : K.B u v = fun y => pd (fun z => m.lower z (K.X z) u) v y
      - ∑ c, m.christoffel c v u y * m.lower y (K.X y) c := rfl
  have hXl := a23_Xl_sm m K
  have hG := a23_chr_sm m
  rw [hB, a23_pd_sub (a23_da (a23_pd_sm (hXl u) v) x)
    (a23_da (by fun_prop) x),
    a23_pd_sum (fun c => a23_da ((hG c v u).mul (hXl c)) x)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => a23_pd_mul (a23_da (hG c v u) x) (a23_da (hXl c) x) a

theorem a23_h4 (m : Spacetime) (K : Congruence m) (x : Pt) (u v : Fin 4) :
    ∑ b, (pd (fun y => K.X y b) v x * K.B u b x + K.X x b * pd (K.B u b) v x) = 0 := by
  have hF : (fun y => ∑ b, K.X y b * K.B u b y) = fun _ => 0 :=
    funext fun y => a23_h3 m K y u
  have h0 : pd (fun y => ∑ b, K.X y b * K.B u b y) v x = 0 := by
    rw [hF]; simp [pd]
  rw [a23_pd_sum (fun b => a23_da ((K.smooth b).mul (a23_B_sm m K u b)) x)] at h0
  rw [← h0]
  exact Finset.sum_congr rfl fun b _ =>
    (a23_pd_mul (a23_da (K.smooth b) x) (a23_da (a23_B_sm m K u b) x) v).symm

theorem a23_chr_symm (m : Spacetime) (y : Pt) (a b c : Fin 4) :
    m.christoffel a b c y = m.christoffel a c b y := by
  unfold Spacetime.christoffel
  have e : (fun z => m.g z b c) = (fun z => m.g z c b) := funext fun z => m.symm z b c
  rw [e]
  congr 1
  exact Finset.sum_congr rfl fun d _ => by ring

open MathematicalRelativity in
theorem solution (m : Spacetime) (K : Congruence m) (x : Pt) (u v : Fin 4) :
    ∑ a, K.X x a * m.covT2 K.B a u v x
      = - (∑ al, ∑ be, K.B u al x * m.ginv x al be * K.B be v x)
        - ∑ ga, ∑ al, m.riemannLower ga u al v x * K.X x ga * K.X x al := by
  have core := a23_core (K.X x) (fun c => m.lower x (K.X x) c)
    (fun a b c => m.christoffel a b c x) (fun a b c d => pd (m.christoffel a b c) d x)
    (fun p q => K.B p q x) (fun p q a => pd (K.B p q) a x)
    (fun b w => pd (fun y => K.X y b) w x) (fun c a => pd (fun y => m.lower y (K.X y) c) a x)
    (fun p q a => pd (pd (fun y => m.lower y (K.X y) p) q) a x)
    (fun i j => m.ginv x i j) (fun i j => m.g x i j) u v
    (fun b a => a23_chr_symm m x b a v)
    (fun c a => by
      show pd (fun y => m.lower y (K.X y) c) a x = K.B c a x + _
      unfold Congruence.B Spacetime.covCov; ring)
    (fun a => a23_h2 m K x u v a) (fun a => a23_h2 m K x u a v)
    (fun a => a23_clairaut (a23_Xl_sm m K u) x v a)
    (fun c => a23_h3 m K x c) (a23_h4 m K x u v) (fun b => a23_h5 m K x b v)
    (fun e => by
      show ∑ ga, m.g x ga e * K.X x ga = m.lower x (K.X x) e
      unfold Spacetime.lower
      exact Finset.sum_congr rfl fun ga _ => by rw [m.symm])
  unfold Spacetime.covT2 Spacetime.riemannLower Spacetime.riemann
  exact core
