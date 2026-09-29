-- Prove2me | solution 1 for MathematicalRelativity.congruence_jacobi_equation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:34:18.752634+00:00
-- url     : https://prove2.me/submissions/1604f5db-568a-47ba-8e63-21cf192b5c6c

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

/-! 4f63aece MathematicalRelativity.congruence_jacobi_equation (Natario Ch. 4).
Route (all in the global chart):
* `ginv_B`: `g^{a al} B_{al nu} = nabla_nu X^a` (metric compatibility of the Christoffel symbols,
  via `g * g^{-1} = 1`, `det g != 0` from the Lorentz normal form).
* Along the curve, `W^a(s) = (nabla_nu X^a)(c s) Y^nu(s)` equals `covDAlong c Y s a` on the open
  set `I`, so its `deriv` is computed by the chain rule (`deriv_comp_curve`) and product rule.
* The geodesic identity `(nabla_b X^a) X^b = 0` and its partial derivative (`geo_deriv`),
  Schwarz for `X` and symmetry of the Christoffel symbols reduce the claim to a pure polynomial
  identity over `Fin 4` sums (`jac_alg`, closed by `linear_combination`).
* Smoothness of `g^{-1}` via `det`/`adjugate` (`ginv_cd`), hence of the Christoffel symbols. -/

set_option autoImplicit false

open scoped ContDiff

namespace JacBuild4f

open MathematicalRelativity

theorem pd_cd {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) : ContDiff ℝ ∞ (pd f i) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by norm_cast)
  exact h1.clm_apply contDiff_const

theorem det_cd (M : Pt → Matrix (Fin 4) (Fin 4) ℝ) (hM : ∀ i j, ContDiff ℝ ∞ (fun x => M x i j)) :
    ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

theorem det_ne (m : Spacetime) (x : Pt) : (m.mat x).det ≠ 0 := by
  obtain ⟨P, _, hPe⟩ := m.lorentz x
  intro h
  have h2 := congrArg Matrix.det hPe
  have h' : (Matrix.of (m.g x)).det = 0 := h
  rw [Matrix.det_mul, Matrix.det_mul, h'] at h2
  simp [eta, Matrix.det_diagonal] at h2

theorem ginv_cd (m : Spacetime) (i j : Fin 4) : ContDiff ℝ ∞ (fun x => m.ginv x i j) := by
  have hdet : ContDiff ℝ ∞ (fun x => (m.mat x).det) := det_cd m.mat (fun i j => m.smooth i j)
  have hadj : ContDiff ℝ ∞ (fun x => (m.mat x).adjugate i j) := by
    simp only [Matrix.adjugate_apply]
    apply det_cd
    intro k l
    by_cases hk : k = j
    · simp only [Matrix.updateRow_apply, hk, if_true]
      exact contDiff_const
    · simp only [Matrix.updateRow_apply, hk, if_false]
      exact m.smooth k l
  have e : (fun x => m.ginv x i j) = fun x => ((m.mat x).det)⁻¹ * (m.mat x).adjugate i j := by
    funext x
    simp [Spacetime.ginv, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  exact (hdet.inv (fun x => det_ne m x)).mul hadj

theorem chr_cd (m : Spacetime) (a b c : Fin 4) : ContDiff ℝ ∞ (m.christoffel a b c) := by
  show ContDiff ℝ ∞ (fun x => m.christoffel a b c x)
  simp only [Spacetime.christoffel]
  exact contDiff_const.mul (ContDiff.sum fun d _ => (ginv_cd m a d).mul
    (((pd_cd (m.smooth d c) b).add (pd_cd (m.smooth d b) c)).sub (pd_cd (m.smooth b c) d)))

theorem chr_symm (m : Spacetime) (a b c : Fin 4) (x : Pt) :
    m.christoffel a b c x = m.christoffel a c b x := by
  unfold Spacetime.christoffel
  have e : (fun y => m.g y b c) = fun y => m.g y c b := funext fun y => m.symm y b c
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem deriv_comp_curve {F : Pt → ℝ} {c : ℝ → Pt} {t : ℝ} (hF : DifferentiableAt ℝ F (c t))
    (hc : ∀ μ, DifferentiableAt ℝ (fun s => c s μ) t) :
    HasDerivAt (fun s => F (c s)) (∑ μ, pd F μ (c t) * vel c t μ) t := by
  have hc' : HasDerivAt c (vel c t) t := hasDerivAt_pi.2 fun μ => (hc μ).hasDerivAt
  have h := hF.hasFDerivAt.comp_hasDerivAt t hc'
  have e : fderiv ℝ F (c t) (vel c t) = ∑ μ, pd F μ (c t) * vel c t μ := by
    conv_lhs => rw [← Finset.univ_sum_single (vel c t)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show (Pi.single μ (vel c t μ) : Pt) = vel c t μ • (Pi.single μ (1:ℝ) : Pt) by
      ext j; simp [Pi.single_apply]]
    rw [map_smul, smul_eq_mul, pd, mul_comm]
  rw [← e]
  exact h

theorem pd_add {f h : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x)
    (i : Fin 4) : pd (fun y => f y + h y) i x = pd f i x + pd h i x := by
  simp only [pd, fderiv_fun_add hf hh, ContinuousLinearMap.add_apply]

theorem pd_mul {f h : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x) (hh : DifferentiableAt ℝ h x)
    (i : Fin 4) : pd (fun y => f y * h y) i x = pd f i x * h x + f x * pd h i x := by
  simp only [pd, fderiv_fun_mul hf hh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_sum {F : Fin 4 → Pt → ℝ} {x : Pt} (hF : ∀ k, DifferentiableAt ℝ (F k) x)
    (i : Fin 4) : pd (fun y => ∑ k, F k y) i x = ∑ k, pd (F k) i x := by
  simp only [pd, fderiv_fun_sum (fun k _ => hF k), ContinuousLinearMap.sum_apply]

theorem g_ginv (m : Spacetime) (x : Pt) (v d : Fin 4) :
    ∑ l, m.g x v l * m.ginv x l d = if v = d then 1 else 0 := by
  have h := Matrix.mul_nonsing_inv (m.mat x) (isUnit_iff_ne_zero.2 (det_ne m x))
  have h2 := congrFun (congrFun h v) d
  simpa [Matrix.mul_apply, Matrix.one_apply, Spacetime.ginv, Spacetime.mat] using h2

theorem ginv_g (m : Spacetime) (x : Pt) (a j : Fin 4) :
    ∑ l, m.ginv x a l * m.g x l j = if a = j then 1 else 0 := by
  have h := Matrix.nonsing_inv_mul (m.mat x) (isUnit_iff_ne_zero.2 (det_ne m x))
  have h2 := congrFun (congrFun h a) j
  simpa [Matrix.mul_apply, Matrix.one_apply, Spacetime.ginv, Spacetime.mat] using h2

set_option maxHeartbeats 4000000 in
theorem jac_alg (a : Fin 4) (X Y : Fin 4 → ℝ) (dX ddX : Fin 4 → Fin 4 → ℝ)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (dG : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsch : ∀ i j, ddX i j = ddX j i)
    (hG1 : ∀ c, ∑ μ, (dX c μ + ∑ f, G c μ f * X f) * X μ = 0)
    (hG2 : ∀ ν, ∑ μ, ((ddX μ ν + ∑ c, (dG μ c ν * X c + G a μ c * dX c ν)) * X μ
        + (dX a μ + ∑ c, G a μ c * X c) * dX μ ν) = 0) :
    ∑ ν, ((∑ μ, (ddX ν μ + ∑ c, (dG ν c μ * X c + G a ν c * dX c μ)) * X μ) * Y ν
        + (dX a ν + ∑ c, G a ν c * X c) *
          ((∑ ρ, (dX ν ρ + ∑ c, G ν ρ c * X c) * Y ρ) - ∑ b, ∑ d, G ν d b * X b * Y d))
      + ∑ b, ∑ d, G a b d * X b * (∑ ν, (dX d ν + ∑ c, G d ν c * X c) * Y ν)
    = ∑ b, ∑ e, ∑ d, (dG d b e - dG e b d
        + ∑ f, (G a e f * G f d b - G a d f * G f e b)) * X b * X e * Y d := by
  have h2 : ∑ ν, Y ν * ∑ μ, ((ddX μ ν + ∑ c, (dG μ c ν * X c + G a μ c * dX c ν)) * X μ
        + (dX a μ + ∑ c, G a μ c * X c) * dX μ ν) = 0 :=
    Finset.sum_eq_zero fun ν _ => by rw [hG2 ν, mul_zero]
  have h1 : ∑ ν, ∑ c, Y ν * G a ν c * ∑ μ, (dX c μ + ∑ f, G c μ f * X f) * X μ = 0 :=
    Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun c _ => by rw [hG1 c, mul_zero]
  have hs : ∑ ν, ∑ μ, Y ν * X μ * (ddX ν μ - ddX μ ν) = 0 :=
    Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun μ _ => by rw [hsch ν μ, sub_self, mul_zero]
  simp only [Fin.sum_univ_four] at h1 h2 hs ⊢
  linear_combination h2 + h1 + hs

theorem jac_alg2 (a : Fin 4) (X Y : Fin 4 → ℝ) (dX ddX : Fin 4 → Fin 4 → ℝ)
    (G : Fin 4 → Fin 4 → Fin 4 → ℝ) (dG : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hsym : ∀ i j k, G i j k = G i k j)
    (hsch : ∀ i j, ddX i j = ddX j i)
    (hG1 : ∀ c, ∑ μ, (dX c μ + ∑ f, G c μ f * X f) * X μ = 0)
    (hG2 : ∀ ν, ∑ μ, ((ddX μ ν + ∑ c, (dG μ c ν * X c + G a μ c * dX c ν)) * X μ
        + (dX a μ + ∑ c, G a μ c * X c) * dX μ ν) = 0) :
    ∑ ν, ((∑ μ, (ddX ν μ + ∑ c, (dG ν c μ * X c + G a ν c * dX c μ)) * X μ) * Y ν
        + (dX a ν + ∑ c, G a ν c * X c) *
          ((∑ ρ, (dX ν ρ + ∑ c, G ν ρ c * X c) * Y ρ) - ∑ b, ∑ d, G ν b d * X b * Y d))
      + ∑ b, ∑ d, G a b d * X b * (∑ ν, (dX d ν + ∑ c, G d ν c * X c) * Y ν)
    = ∑ b, ∑ e, ∑ d, (dG d b e - dG e b d
        + ∑ f, (G a e f * G f d b - G a d f * G f e b)) * X b * X e * Y d := by
  have e : ∀ ν, ∑ b, ∑ d, G ν b d * X b * Y d = ∑ b, ∑ d, G ν d b * X b * Y d := fun ν =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [hsym]
  simp only [e]
  exact jac_alg a X Y dX ddX G dG hsch hG1 hG2

theorem g_chr (m : Spacetime) (x : Pt) (v u j : Fin 4) :
    ∑ l, m.g x v l * m.christoffel l u j x =
      (1/2) * (pd (fun y => m.g y v j) u x + pd (fun y => m.g y v u) j x
        - pd (fun y => m.g y u j) v x) := by
  have key : ∀ E : Fin 4 → ℝ,
      ∑ l, m.g x v l * ((1/2:ℝ) * ∑ d, m.ginv x l d * E d) = (1/2) * E v := by
    intro E
    have h1 : ∑ l, m.g x v l * ((1/2:ℝ) * ∑ d, m.ginv x l d * E d)
        = (1/2) * ∑ d, (∑ l, m.g x v l * m.ginv x l d) * E d := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [h1]
    simp [g_ginv]
  exact key (fun d => pd (fun y => m.g y d j) u x + pd (fun y => m.g y d u) j x
    - pd (fun y => m.g y u j) d x)

theorem metric_compat (m : Spacetime) (x : Pt) (u v j : Fin 4) :
    pd (fun y => m.g y v j) u x
      = ∑ l, m.g x v l * m.christoffel l u j x + ∑ l, m.g x l j * m.christoffel l u v x := by
  have e2 : ∑ l, m.g x l j * m.christoffel l u v x = ∑ l, m.g x j l * m.christoffel l u v x :=
    Finset.sum_congr rfl fun l _ => by rw [m.symm x l j]
  rw [e2, g_chr, g_chr]
  rw [show (fun y => m.g y j v) = (fun y => m.g y v j) from funext fun y => m.symm y j v,
      show (fun y => m.g y j u) = (fun y => m.g y u j) from funext fun y => m.symm y j u,
      show (fun y => m.g y u v) = (fun y => m.g y v u) from funext fun y => m.symm y u v]
  ring

theorem B_lower (m : Spacetime) (K : Congruence m) (al nu : Fin 4) (x : Pt) :
    K.B al nu x = ∑ l, m.g x al l * m.covVec K.X l nu x := by
  have hd : ∀ j, DifferentiableAt ℝ (fun y => m.g y al j * K.X y j) x := fun j =>
    (((m.smooth al j).mul (K.smooth j)).differentiable (by simp)) x
  have e1 : pd (fun y => m.lower y (K.X y) al) nu x
      = ∑ j, (pd (fun y => m.g y al j) nu x * K.X x j
          + m.g x al j * pd (fun y => K.X y j) nu x) := by
    unfold Spacetime.lower
    rw [pd_sum hd]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact pd_mul (((m.smooth al j).differentiable (by simp)) x)
      (((K.smooth j).differentiable (by simp)) x) nu
  simp only [Congruence.B, Spacetime.covCov, e1, metric_compat m x nu al]
  simp only [Spacetime.lower, Spacetime.covVec, Fin.sum_univ_four]
  ring

theorem ginv_B (m : Spacetime) (K : Congruence m) (a nu : Fin 4) (x : Pt) :
    ∑ al, m.ginv x a al * K.B al nu x = m.covVec K.X a nu x := by
  simp only [B_lower, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ l, ∑ al, m.ginv x a al * (m.g x al l * m.covVec K.X l nu x)
      = (∑ al, m.ginv x a al * m.g x al l) * m.covVec K.X l nu x := by
    intro l; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun al _ => ?_; ring
  simp only [h, ginv_g]
  simp

theorem covVec_cd (m : Spacetime) (K : Congruence m) (a μ : Fin 4) :
    ContDiff ℝ ∞ (m.covVec K.X a μ) := by
  show ContDiff ℝ ∞ (fun y => pd (fun y => K.X y a) μ y + ∑ c, m.christoffel a μ c y * K.X y c)
  exact (pd_cd (K.smooth a) μ).add (ContDiff.sum fun c _ => (chr_cd m a μ c).mul (K.smooth c))

theorem pd_covVec (m : Spacetime) (K : Congruence m) (a μ ν : Fin 4) (x : Pt) :
    pd (m.covVec K.X a μ) ν x = pd (pd (fun y => K.X y a) μ) ν x
      + ∑ c, (pd (m.christoffel a μ c) ν x * K.X x c
          + m.christoffel a μ c x * pd (fun y => K.X y c) ν x) := by
  have e : m.covVec K.X a μ
      = fun y => pd (fun y => K.X y a) μ y + ∑ c, m.christoffel a μ c y * K.X y c := rfl
  have hd1 : DifferentiableAt ℝ (pd (fun y => K.X y a) μ) x :=
    ((pd_cd (K.smooth a) μ).differentiable (by simp)) x
  have hd2 : DifferentiableAt ℝ (fun y => ∑ c, m.christoffel a μ c y * K.X y c) x :=
    ((ContDiff.sum fun c _ => (chr_cd m a μ c).mul (K.smooth c)).differentiable (by simp)) x
  have hd3 : ∀ c, DifferentiableAt ℝ (fun y => m.christoffel a μ c y * K.X y c) x := fun c =>
    (((chr_cd m a μ c).mul (K.smooth c)).differentiable (by simp)) x
  rw [e, pd_add hd1 hd2, pd_sum hd3]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact pd_mul (((chr_cd m a μ c).differentiable (by simp)) x)
    (((K.smooth c).differentiable (by simp)) x) ν

theorem geo_deriv (m : Spacetime) (K : Congruence m) (a ν : Fin 4) (x : Pt) :
    ∑ μ, (pd (m.covVec K.X a μ) ν x * K.X x μ
      + m.covVec K.X a μ x * pd (fun y => K.X y μ) ν x) = 0 := by
  have hz : (fun y => ∑ b, m.covVec K.X a b y * K.X y b) = fun _ => 0 :=
    funext fun y => K.geodesic y a
  have h0 : pd (fun y => ∑ b, m.covVec K.X a b y * K.X y b) ν x = 0 := by
    rw [hz]; simp [pd]
  have hd : ∀ b, DifferentiableAt ℝ (fun y => m.covVec K.X a b y * K.X y b) x := fun b =>
    (((covVec_cd m K a b).mul (K.smooth b)).differentiable (by simp)) x
  rw [pd_sum hd] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact (pd_mul (((covVec_cd m K a μ).differentiable (by simp)) x)
    (((K.smooth μ).differentiable (by simp)) x) ν).symm

theorem schwarz {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 4) (x : Pt) :
    pd (pd f i) j x = pd (pd f j) i x := by
  have hs : IsSymmSndFDerivAt ℝ f x :=
    (hf.contDiffAt (x := x)).isSymmSndFDerivAt (n := ∞)
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
  have hd : ∀ y, DifferentiableAt ℝ (fderiv ℝ f) y := fun y =>
    ((hf.fderiv_right (m := ∞) (by norm_cast)).differentiable (by simp)) y
  have e : ∀ k l, pd (pd f k) l x = fderiv ℝ (fderiv ℝ f) x (Pi.single l 1) (Pi.single k 1) := by
    intro k l
    show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single k 1)) x (Pi.single l 1) = _
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [e, e]
  exact hs _ _

end JacBuild4f

open MathematicalRelativity in
theorem solution
    (m : Spacetime) (K : Congruence m) (c Y : ℝ → Pt) (I : Set ℝ)
    (hI : IsOpen I)
    (hc : K.IsIntegralCurveOn c I)
    (hY : ∀ a, ContDiffOn ℝ 2 (fun s => Y s a) I)
    (hdev : ∀ t ∈ I, ∀ a, m.covDAlong c Y t a
      = ∑ al, ∑ nu, m.ginv (c t) a al * K.B al nu (c t) * Y t nu) :
    m.IsJacobiFieldOn c Y I := by
  refine ⟨hY, fun t ht a => ?_⟩
  have hF1 : ∀ s ∈ I, ∀ ν, m.covDAlong c Y s ν = ∑ μ, m.covVec K.X ν μ (c s) * Y s μ := by
    intro s hs ν
    rw [hdev s hs ν, Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_mul, JacBuild4f.ginv_B]
  have hcd : ∀ μ, DifferentiableAt ℝ (fun s => c s μ) t := fun μ =>
    ((hc.1 μ).contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)
  have hYd : ∀ μ, DifferentiableAt ℝ (fun s => Y s μ) t := fun μ =>
    ((hY μ).contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)
  have hF2 : deriv (fun s => m.covDAlong c Y s a) t
      = deriv (fun s => ∑ μ, m.covVec K.X a μ (c s) * Y s μ) t :=
    Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (hI.mem_nhds ht) fun s hs => hF1 s hs a)
  have hF3 : HasDerivAt (fun s => ∑ μ, m.covVec K.X a μ (c s) * Y s μ)
      (∑ ν, ((∑ μ, pd (m.covVec K.X a ν) μ (c t) * vel c t μ) * Y t ν
        + m.covVec K.X a ν (c t) * deriv (fun s => Y s ν) t)) t :=
    HasDerivAt.fun_sum fun ν _ =>
      (JacBuild4f.deriv_comp_curve
        (((JacBuild4f.covVec_cd m K a ν).differentiable (by simp)) (c t)) hcd).mul
        (hYd ν).hasDerivAt
  have hF4 : ∀ ν, deriv (fun s => Y s ν) t = (∑ μ, m.covVec K.X ν μ (c t) * Y t μ)
      - ∑ b, ∑ d, m.christoffel ν b d (c t) * vel c t b * Y t d := by
    intro ν
    have h := hF1 t ht ν
    simp only [Spacetime.covDAlong] at h
    linarith
  have hvel : vel c t = K.X (c t) := hc.2 t ht
  have hG1 : ∀ c', ∑ μ, (pd (fun y => K.X y c') μ (c t)
      + ∑ f, m.christoffel c' μ f (c t) * K.X (c t) f) * K.X (c t) μ = 0 :=
    fun c' => K.geodesic (c t) c'
  have hG2 : ∀ ν, ∑ μ, ((pd (pd (fun y => K.X y a) μ) ν (c t)
      + ∑ c', (pd (m.christoffel a μ c') ν (c t) * K.X (c t) c'
        + m.christoffel a μ c' (c t) * pd (fun y => K.X y c') ν (c t))) * K.X (c t) μ
      + (pd (fun y => K.X y a) μ (c t) + ∑ c', m.christoffel a μ c' (c t) * K.X (c t) c')
        * pd (fun y => K.X y μ) ν (c t)) = 0 := by
    intro ν
    have h := JacBuild4f.geo_deriv m K a ν (c t)
    simp only [JacBuild4f.pd_covVec m K a] at h
    exact h
  have hsch : ∀ i j, pd (pd (fun y => K.X y a) i) j (c t) = pd (pd (fun y => K.X y a) j) i (c t) :=
    fun i j => JacBuild4f.schwarz (K.smooth a) i j (c t)
  have hsym : ∀ i j k, m.christoffel i j k (c t) = m.christoffel i k j (c t) :=
    fun i j k => JacBuild4f.chr_symm m i j k (c t)
  rw [show m.covDAlong c (m.covDAlong c Y) t a = deriv (fun s => m.covDAlong c Y s a) t
      + ∑ b, ∑ d, m.christoffel a b d (c t) * vel c t b * m.covDAlong c Y t d from rfl]
  rw [hF2, hF3.deriv]
  simp only [hF1 t ht, hF4, JacBuild4f.pd_covVec m K a]
  rw [hvel]
  exact JacBuild4f.jac_alg2 a (K.X (c t)) (Y t) (fun i j => pd (fun y => K.X y i) j (c t))
    (fun i j => pd (pd (fun y => K.X y a) i) j (c t)) (fun i j k => m.christoffel i j k (c t))
    (fun i j k => pd (m.christoffel a i j) k (c t)) hsym hsch hG1 hG2
