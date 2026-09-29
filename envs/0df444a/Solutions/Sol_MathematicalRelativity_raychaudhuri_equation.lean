-- Prove2me | solution 1 for MathematicalRelativity.raychaudhuri_equation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:47:54.793172+00:00
-- url     : https://prove2.me/submissions/e4e0d311-2562-457b-8738-3d19e2a7517f

import Mathlib
import Definitions.Def_natario_gr_core
import Definitions.Def_natario_gr_curves
import Definitions.Def_natario_gr_congruence
import Definitions.Def_natario_gr_causality

/-! c41b76a1 MathematicalRelativity.raychaudhuri_equation (Natario, Prop. 4.1.5).
Coordinate proof in the global chart.
* `B_eq`: metric compatibility of the Levi-Civita Christoffel symbols gives
  `B_{uv} = g_{ue} D^e_v` with `D^a_b = ∇_b X^a` (`covVec`); hence `θ = tr D` (`expansion_eq`).
* `lin_alg`: with `Gi = g⁻¹`, `D X = 0` (geodesic) and `g(X,X) = -1`, the pairing
  `pr Gi P Q = tr(Pᵀ Gi Q Gi)` gives `σ² - ω² + θ²/3 = tr(D D)`.
* `final_alg`: differentiating `θ = ∂_a X^a + Γ^a_{ae} X^e` along `X`, and the derivative of the
  geodesic equation, gives `X·θ = -tr(D D) - Ric(X, X)` (symmetric second derivatives,
  symmetric Christoffel symbols).
* `contDiff_ginv`: `g⁻¹ = det⁻¹ • adj` is smooth since `det g ≠ 0` (Lorentz signature). -/

set_option autoImplicit false

open scoped ContDiff

namespace RayBuild

open MathematicalRelativity Matrix

theorem pd_add {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  simp [pd, fderiv_fun_add hf hg]

theorem pd_mul {f g : Pt → ℝ} {x : Pt} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  simp [pd, fderiv_fun_mul hf hg]; ring

theorem pd_sum {F : Fin 4 → Pt → ℝ} {x : Pt} (h : ∀ k, DifferentiableAt ℝ (F k) x)
    (i : Fin 4) :
    pd (fun y => ∑ k, F k y) i x = ∑ k, pd (F k) i x := by
  simp [pd, fderiv_fun_sum (fun k _ => h k)]

theorem pd_zero (i : Fin 4) (x : Pt) : pd (fun _ => (0 : ℝ)) i x = 0 := by
  simp [pd]

theorem contDiff_pd {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (pd f i) := by
  unfold pd
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem pd_pd_comm {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (a b : Fin 4) (x : Pt) :
    pd (pd f a) b x = pd (pd f b) a x := by
  have hs : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by simpa using two_le_infty)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  unfold pd
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp
  exact hs _ _

theorem contDiff_det {M : Pt → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ ∞ (fun x => M x i j)) :
    ContDiff ℝ ∞ (fun x => (M x).det) := by
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem det_ne (m : Spacetime) (x : Pt) : (m.mat x).det ≠ 0 := by
  obtain ⟨P, _, h⟩ := m.lorentz x
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  intro h0
  have h0' : (Matrix.of (m.g x)).det = 0 := h0
  rw [h0'] at h2
  simp [eta, Matrix.det_diagonal] at h2

theorem contDiff_ginv (m : Spacetime) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x => m.ginv x i j) := by
  have hg : ∀ a b, ContDiff ℝ ∞ (fun x => m.mat x a b) := fun a b => m.smooth a b
  have hdet : ContDiff ℝ ∞ (fun x => (m.mat x).det) := contDiff_det hg
  have hadj : ContDiff ℝ ∞ (fun x => (m.mat x).adjugate i j) := by
    simp_rw [Matrix.adjugate_apply]
    apply contDiff_det
    intro a b
    by_cases hab : a = j
    · subst hab; simp only [Matrix.updateRow_self]; exact contDiff_const
    · simp only [Matrix.updateRow_ne hab]; exact hg a b
  have e : (fun x => m.ginv x i j) = fun x => ((m.mat x).det)⁻¹ * (m.mat x).adjugate i j := by
    funext x
    simp [Spacetime.ginv, Matrix.inv_def, Ring.inverse_eq_inv]
  rw [e]
  exact (hdet.inv (fun x => det_ne m x)).mul hadj


theorem dAt {f : Pt → ℝ} (hf : ContDiff ℝ ∞ f) (x : Pt) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by simp)) x

section Metric

variable (m : Spacetime)

theorem mat_symm (x : Pt) : (m.mat x)ᵀ = m.mat x := by
  ext i j; simp [Spacetime.mat, m.symm x j i]

theorem mat_isUnit (x : Pt) : IsUnit (m.mat x).det := isUnit_iff_ne_zero.mpr (det_ne m x)

theorem mat_mul_inv (x : Pt) : m.mat x * (m.mat x)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (mat_isUnit m x)

theorem inv_mul_mat (x : Pt) : (m.mat x)⁻¹ * m.mat x = 1 :=
  Matrix.nonsing_inv_mul _ (mat_isUnit m x)

theorem inv_symm (x : Pt) : ((m.mat x)⁻¹)ᵀ = (m.mat x)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, mat_symm]

theorem ginv_symm (x : Pt) (u v : Fin 4) : m.ginv x u v = m.ginv x v u := by
  have h := congrFun (congrFun (inv_symm m x) v) u
  rw [Matrix.transpose_apply] at h
  exact h

theorem contract (x : Pt) (T : Fin 4 → ℝ) (a : Fin 4) :
    ∑ e, m.g x a e * ∑ d, m.ginv x e d * T d = T a := by
  have h : (m.mat x *ᵥ ((m.mat x)⁻¹ *ᵥ T)) a
      = ∑ e, m.g x a e * ∑ d, m.ginv x e d * T d := rfl
  rw [← h, Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]

theorem contract' (x : Pt) (T : Fin 4 → ℝ) (v : Fin 4) :
    ∑ u, m.ginv x v u * ∑ e, m.g x u e * T e = T v := by
  have h : ((m.mat x)⁻¹ *ᵥ (m.mat x *ᵥ T)) v
      = ∑ u, m.ginv x v u * ∑ e, m.g x u e * T e := rfl
  rw [← h, Matrix.mulVec_mulVec, inv_mul_mat, Matrix.one_mulVec]

theorem pd_g_symm (a b c : Fin 4) (x : Pt) :
    pd (fun y => m.g y a b) c x = pd (fun y => m.g y b a) c x := by
  have : (fun y => m.g y a b) = (fun y => m.g y b a) := funext fun y => m.symm y a b
  rw [this]

theorem lower_christoffel (x : Pt) (a c b : Fin 4) :
    ∑ e, m.g x a e * m.christoffel e c b x
      = (1/2 : ℝ) * (pd (fun y => m.g y a b) c x + pd (fun y => m.g y a c) b x
          - pd (fun y => m.g y c b) a x) := by
  have h := contract m x (fun d => pd (fun y => m.g y d b) c x + pd (fun y => m.g y d c) b x
          - pd (fun y => m.g y c b) d x) a
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Spacetime.christoffel]
  ring

theorem metric_compat (x : Pt) (a b c : Fin 4) :
    pd (fun y => m.g y a b) c x
      = ∑ e, (m.g x a e * m.christoffel e c b x + m.g x b e * m.christoffel e c a x) := by
  rw [Finset.sum_add_distrib, lower_christoffel, lower_christoffel,
    pd_g_symm m b a c, pd_g_symm m b c a, pd_g_symm m c a b]
  ring

theorem christoffel_symm (a b c : Fin 4) : m.christoffel a b c = m.christoffel a c b := by
  funext x
  simp only [Spacetime.christoffel]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pd_g_symm m b c d]
  ring

theorem contDiff_christoffel (a b c : Fin 4) : ContDiff ℝ ∞ (m.christoffel a b c) := by
  have hg : ∀ i j, ContDiff ℝ ∞ (fun y => m.g y i j) := m.smooth
  unfold Spacetime.christoffel
  refine contDiff_const.mul (ContDiff.sum fun d _ => (contDiff_ginv m a d).mul ?_)
  exact ((contDiff_pd (hg _ _) _).add (contDiff_pd (hg _ _) _)).sub (contDiff_pd (hg _ _) _)

end Metric

section LinAlg

open Matrix

/-- The pairing `P_{uv} Q^{uv}` in trace form. -/
def pr (Gi P Q : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := trace (Pᵀ * Gi * Q * Gi)

variable (Gi : Matrix (Fin 4) (Fin 4) ℝ)

theorem pr_add_left (P P' Q : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi (P + P') Q = pr Gi P Q + pr Gi P' Q := by
  simp [pr, Matrix.add_mul, Matrix.trace_add]

theorem pr_add_right (P Q Q' : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi P (Q + Q') = pr Gi P Q + pr Gi P Q' := by
  simp [pr, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]

theorem pr_sub_left (P P' Q : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi (P - P') Q = pr Gi P Q - pr Gi P' Q := by
  simp [pr, Matrix.sub_mul, Matrix.trace_sub]

theorem pr_sub_right (P Q Q' : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi P (Q - Q') = pr Gi P Q - pr Gi P Q' := by
  simp [pr, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]

theorem pr_smul_left (c : ℝ) (P Q : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi (c • P) Q = c * pr Gi P Q := by
  simp [pr, Matrix.trace_smul]

theorem pr_smul_right (c : ℝ) (P Q : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi P (c • Q) = c * pr Gi P Q := by
  simp [pr, Matrix.trace_smul]

theorem pr_transpose (hGi : Giᵀ = Gi) (P Q : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi P Q = pr Gi Pᵀ Qᵀ := by
  unfold pr
  rw [← Matrix.trace_transpose (Pᵀ * Gi * Q * Gi)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hGi]
  rw [show Gi * (Qᵀ * (Gi * P)) = (Gi * Qᵀ * Gi) * P by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pr_comm (hGi : Giᵀ = Gi) (P Q : Matrix (Fin 4) (Fin 4) ℝ) :
    pr Gi P Q = pr Gi Q P := by
  unfold pr
  rw [← Matrix.trace_transpose (Pᵀ * Gi * Q * Gi)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hGi]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem lin_alg (G Gi D : Matrix (Fin 4) (Fin 4) ℝ) (Xc : Matrix (Fin 4) (Fin 1) ℝ)
    (hG : Gᵀ = G) (hGi : Giᵀ = Gi) (h1 : G * Gi = 1) (h2 : Gi * G = 1)
    (hDX : D * Xc = 0) (hunit : Xcᵀ * (G * Xc) = -1) :
    pr Gi ((1/2 : ℝ) • (G * D + (G * D)ᵀ) - (trace D / 3) • (G + G * Xc * (Xcᵀ * G)))
         ((1/2 : ℝ) • (G * D + (G * D)ᵀ) - (trace D / 3) • (G + G * Xc * (Xcᵀ * G)))
      - pr Gi ((1/2 : ℝ) • (G * D - (G * D)ᵀ)) ((1/2 : ℝ) • (G * D - (G * D)ᵀ))
      + (trace D) ^ 2 / 3 = trace (D * D) := by
  have h1' : ∀ {n : Type} [Fintype n] (M : Matrix (Fin 4) n ℝ), G * (Gi * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2' : ∀ {n : Type} [Fintype n] (M : Matrix (Fin 4) n ℝ), Gi * (G * M) = M :=
    fun M => by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hDX' : ∀ {n : Type} [Fintype n] (M : Matrix (Fin 1) n ℝ), D * (Xc * M) = 0 :=
    fun M => by rw [← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have hunit' : ∀ {n : Type} [Fintype n] (M : Matrix (Fin 1) n ℝ),
      Xcᵀ * (G * (Xc * M)) = -M :=
    fun M => by rw [← Matrix.mul_assoc G, ← Matrix.mul_assoc, hunit, Matrix.neg_mul,
      Matrix.one_mul]
  have htr : trace (G * (Xc * Xcᵀ)) = -1 := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, hunit]
    simp
  set B := G * D with hB
  set h := G + G * Xc * (Xcᵀ * G) with hh
  have hht : hᵀ = h := by
    simp [hh, Matrix.transpose_add, Matrix.transpose_mul, hG, Matrix.mul_assoc]
  have F2 : pr Gi Bᵀ B = trace (D * D) := by
    simp only [pr, Matrix.transpose_transpose, hB, Matrix.mul_assoc, h2']
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
  have F1 : pr Gi B Bᵀ = trace (D * D) := by
    rw [pr_transpose Gi hGi, Matrix.transpose_transpose, F2]
  have F4 : pr Gi Bᵀ h = trace D := by
    simp only [pr, Matrix.transpose_transpose, hB, hh, Matrix.mul_add,
      Matrix.mul_assoc, h1, h2', Matrix.mul_one, hDX', Matrix.mul_zero,
      add_zero]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one]
  have F3 : pr Gi B h = trace D := by
    rw [pr_transpose Gi hGi, hht, F4]
  have F5 : pr Gi h h = 3 := by
    simp only [pr, hht]
    simp only [hh, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one,
      hunit', Matrix.trace_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, htr,
      Matrix.trace_one]
    norm_num
    linarith [htr]
  simp only [pr_sub_left, pr_sub_right, pr_add_left, pr_add_right, pr_smul_left,
    pr_smul_right]
  rw [pr_comm Gi hGi h B, pr_comm Gi hGi h Bᵀ, F1, F2, F3, F4, F5]
  ring

theorem pair_eq (Gi P Q : Matrix (Fin 4) (Fin 4) ℝ) (hGi : Giᵀ = Gi) :
    ∑ u, ∑ v, ∑ p, ∑ q, Gi u p * Gi v q * P u v * Q p q = pr Gi P Q := by
  have hs : ∀ i j, Gi i j = Gi j i := fun i j => by
    rw [← Matrix.transpose_apply Gi j i, hGi]
  simp only [pr, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_four]
  simp only [hs 1 0, hs 2 0, hs 3 0, hs 2 1, hs 3 1, hs 3 2]
  ring

end LinAlg

set_option maxHeartbeats 4000000 in
theorem final_alg (X : Fin 4 → ℝ) (dX : Fin 4 → Fin 4 → ℝ) (ddX : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (dΓ : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hdd : ∀ a b c, ddX a b c = ddX a c b) (hΓ : ∀ a b c, Γ a b c = Γ a c b)
    (hdΓ : ∀ a b c d, dΓ a b c d = dΓ a c b d)
    (hgeo : ∀ a, ∑ b, (dX a b + ∑ c, Γ a b c * X c) * X b = 0)
    (hgeo2 : ∑ a, ∑ b, ((ddX a b a + ∑ c, (dΓ a b c a * X c + Γ a b c * dX c a)) * X b
        + (dX a b + ∑ c, Γ a b c * X c) * dX b a) = 0) :
    ∑ c, X c * ∑ a, (ddX a a c + ∑ e, (dΓ a a e c * X e + Γ a a e * dX e c))
      = - ∑ a, ∑ b, (dX a b + ∑ c, Γ a b c * X c) * (dX b a + ∑ c, Γ b a c * X c)
        - ∑ i, ∑ j, (∑ a, (dΓ a j i a - dΓ a a i j
            + ∑ e, (Γ a a e * Γ e j i - Γ a j e * Γ e a i))) * X i * X j := by
  have e0 := hgeo 0
  have e1 := hgeo 1
  have e2 := hgeo 2
  have e3 := hgeo 3
  simp only [Fin.sum_univ_four] at e0 e1 e2 e3 hgeo2 ⊢
  simp only [hdd _ 1 0, hdd _ 2 0, hdd _ 3 0, hdd _ 2 1, hdd _ 3 1, hdd _ 3 2,
    hΓ _ 1 0, hΓ _ 2 0, hΓ _ 3 0, hΓ _ 2 1, hΓ _ 3 1, hΓ _ 3 2,
    hdΓ _ 1 0, hdΓ _ 2 0, hdΓ _ 3 0, hdΓ _ 2 1, hdΓ _ 3 1, hdΓ _ 3 2] at e0 e1 e2 e3 hgeo2 ⊢
  linear_combination hgeo2
    + (Γ 0 0 0 + Γ 1 0 1 + Γ 2 0 2 + Γ 3 0 3) * e0
    + (Γ 0 0 1 + Γ 1 1 1 + Γ 2 1 2 + Γ 3 1 3) * e1
    + (Γ 0 0 2 + Γ 1 1 2 + Γ 2 2 2 + Γ 3 2 3) * e2
    + (Γ 0 0 3 + Γ 1 1 3 + Γ 2 2 3 + Γ 3 3 3) * e3

section Cong

variable {m : Spacetime} (K : Congruence m)

theorem contDiff_covVec (a b : Fin 4) : ContDiff ℝ ∞ (m.covVec K.X a b) := by
  unfold Spacetime.covVec
  exact (contDiff_pd (K.smooth a) b).add
    (ContDiff.sum fun c _ => (contDiff_christoffel m a b c).mul (K.smooth c))

theorem pd_covVec (a b i : Fin 4) (x : Pt) :
    pd (m.covVec K.X a b) i x = pd (pd (fun y => K.X y a) b) i x
      + ∑ c, (pd (m.christoffel a b c) i x * K.X x c
          + m.christoffel a b c x * pd (fun y => K.X y c) i x) := by
  have e : m.covVec K.X a b
      = fun y => pd (fun z => K.X z a) b y + ∑ c, m.christoffel a b c y * K.X y c := rfl
  rw [e, pd_add (dAt (contDiff_pd (K.smooth a) b) x)
    (dAt (ContDiff.sum fun c _ => (contDiff_christoffel m a b c).mul (K.smooth c)) x)]
  rw [pd_sum (fun c => dAt ((contDiff_christoffel m a b c).mul (K.smooth c)) x)]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  exact pd_mul (dAt (contDiff_christoffel m a b c) x) (dAt (K.smooth c) x) i

theorem B_eq (u v : Fin 4) (x : Pt) :
    K.B u v x = ∑ e, m.g x u e * m.covVec K.X e v x := by
  have hs : ∀ j, pd (fun y => m.g y u j * K.X y j) v x
      = pd (fun y => m.g y u j) v x * K.X x j + m.g x u j * pd (fun y => K.X y j) v x :=
    fun j => pd_mul (dAt (m.smooth u j) x) (dAt (K.smooth j) x) v
  simp only [Congruence.B, Spacetime.covCov, Spacetime.lower]
  rw [pd_sum (fun j => dAt ((m.smooth u j).mul (K.smooth j)) x)]
  simp only [hs, metric_compat m x, Spacetime.covVec, Fin.sum_univ_four]
  simp only [m.symm x 1 0, m.symm x 2 0, m.symm x 3 0, m.symm x 2 1, m.symm x 3 1,
    m.symm x 3 2]
  ring

theorem expansion_eq (y : Pt) : K.expansion y = ∑ a, m.covVec K.X a a y := by
  simp only [Congruence.expansion, B_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Eq.trans ?_ (contract' m y (fun e => m.covVec K.X e v y) v)
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [ginv_symm m y u v]

theorem expansion_fun : K.expansion = fun y => ∑ a, m.covVec K.X a a y :=
  funext (expansion_eq K)

end Cong

theorem raychaudhuri_main
    (m : Spacetime) (K : Congruence m) (x : Pt) :
    K.along K.expansion x
      = - (1/3 : ℝ) * (K.expansion x) ^ 2 - K.shearSq x + K.vorticitySq x
        - m.ricciQuad x (K.X x) := by
  have hG : (m.mat x)ᵀ = m.mat x := mat_symm m x
  have hGi : ((m.mat x)⁻¹)ᵀ = (m.mat x)⁻¹ := inv_symm m x
  have h1 : m.mat x * (m.mat x)⁻¹ = 1 := mat_mul_inv m x
  have h2 : (m.mat x)⁻¹ * m.mat x = 1 := inv_mul_mat m x
  let D : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun a b => m.covVec K.X a b x
  let Xc : Matrix (Fin 4) (Fin 1) ℝ := Matrix.replicateCol (Fin 1) (K.X x)
  have hDX : D * Xc = 0 := by
    ext i k
    simp only [D, Xc, Matrix.mul_apply, Matrix.of_apply, Matrix.replicateCol_apply,
      Matrix.zero_apply]
    exact K.geodesic x i
  have hunit : Xcᵀ * (m.mat x * Xc) = -1 := by
    ext i k
    have hik : i = k := Subsingleton.elim _ _
    subst hik
    have hu := K.unit x
    simp only [Spacetime.ip] at hu
    simp only [Xc, Matrix.mul_apply, Matrix.transpose_apply, Matrix.replicateCol_apply,
      Matrix.neg_apply, Matrix.one_apply_eq, Spacetime.mat, Matrix.of_apply]
    rw [← hu]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hθ : K.expansion x = trace D := by
    rw [expansion_eq K x]
    rfl
  have hB : ∀ u v, K.B u v x = (m.mat x * D) u v := by
    intro u v
    rw [B_eq K u v x]
    rfl
  have hh : ∀ u v, K.h u v x = (m.mat x + m.mat x * Xc * (Xcᵀ * m.mat x)) u v := by
    intro u v
    have hl : ∀ w, m.lower x (K.X x) w = ∑ j, K.X x j * m.g x j w := fun w =>
      Finset.sum_congr rfl fun j _ => by rw [m.symm x w j, mul_comm]
    simp only [Congruence.h, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Xc, Matrix.replicateCol_apply, Spacetime.mat, Matrix.of_apply, Finset.univ_unique,
      Finset.sum_singleton]
    rw [hl v]
    rfl
  have hshear : ∀ u v, K.shear u v x
      = ((1/2 : ℝ) • (m.mat x * D + (m.mat x * D)ᵀ)
          - (trace D / 3) • (m.mat x + m.mat x * Xc * (Xcᵀ * m.mat x))) u v := by
    intro u v
    simp only [Congruence.shear, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.transpose_apply, smul_eq_mul, hB, hθ]
    rw [hh u v]
    rfl
  have hvort : ∀ u v, K.vorticity u v x
      = ((1/2 : ℝ) • (m.mat x * D - (m.mat x * D)ᵀ)) u v := by
    intro u v
    simp only [Congruence.vorticity, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, hB]
  have hsh : K.shearSq x = pr (m.mat x)⁻¹
      ((1/2 : ℝ) • (m.mat x * D + (m.mat x * D)ᵀ)
          - (trace D / 3) • (m.mat x + m.mat x * Xc * (Xcᵀ * m.mat x)))
      ((1/2 : ℝ) • (m.mat x * D + (m.mat x * D)ᵀ)
          - (trace D / 3) • (m.mat x + m.mat x * Xc * (Xcᵀ * m.mat x))) := by
    simp only [Congruence.shearSq, hshear]
    exact pair_eq _ _ _ hGi
  have hvo : K.vorticitySq x = pr (m.mat x)⁻¹
      ((1/2 : ℝ) • (m.mat x * D - (m.mat x * D)ᵀ))
      ((1/2 : ℝ) • (m.mat x * D - (m.mat x * D)ᵀ)) := by
    simp only [Congruence.vorticitySq, hvort]
    exact pair_eq _ _ _ hGi
  have hL := lin_alg (m.mat x) (m.mat x)⁻¹ D Xc hG hGi h1 h2 hDX hunit
  -- the analytic part
  have hz : ∀ a, pd (fun y => ∑ b, m.covVec K.X a b y * K.X y b) a x = 0 := fun a => by
    have e : (fun y => ∑ b, m.covVec K.X a b y * K.X y b) = fun _ => 0 :=
      funext fun y => K.geodesic y a
    rw [e, pd_zero]
  have hexp : ∀ a, pd (fun y => ∑ b, m.covVec K.X a b y * K.X y b) a x
      = ∑ b, (pd (m.covVec K.X a b) a x * K.X x b
          + m.covVec K.X a b x * pd (fun y => K.X y b) a x) := fun a => by
    rw [pd_sum (fun b => dAt ((contDiff_covVec K a b).mul (K.smooth b)) x)]
    exact Finset.sum_congr rfl fun b _ =>
      pd_mul (dAt (contDiff_covVec K a b) x) (dAt (K.smooth b) x) a
  have hgeo2 : ∑ a, ∑ b, ((pd (pd (fun y => K.X y a) b) a x
      + ∑ c, (pd (m.christoffel a b c) a x * K.X x c
        + m.christoffel a b c x * pd (fun y => K.X y c) a x)) * K.X x b
      + (pd (fun y => K.X y a) b x + ∑ c, m.christoffel a b c x * K.X x c)
        * pd (fun y => K.X y b) a x) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← hz a, hexp a]
    simp only [pd_covVec K]
    rfl
  have hLHS : K.along K.expansion x = ∑ c, K.X x c * ∑ a, (pd (pd (fun y => K.X y a) a) c x
      + ∑ e, (pd (m.christoffel a a e) c x * K.X x e
        + m.christoffel a a e x * pd (fun y => K.X y e) c x)) := by
    simp only [Congruence.along]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [expansion_fun K, pd_sum (fun a => dAt (contDiff_covVec K a a) x)]
    exact Finset.sum_congr rfl fun a _ => pd_covVec K a a c x
  have hF : ∑ c, K.X x c * ∑ a, (pd (pd (fun y => K.X y a) a) c x
      + ∑ e, (pd (m.christoffel a a e) c x * K.X x e
        + m.christoffel a a e x * pd (fun y => K.X y e) c x))
      = - ∑ a, ∑ b, (pd (fun y => K.X y a) b x + ∑ c, m.christoffel a b c x * K.X x c)
          * (pd (fun y => K.X y b) a x + ∑ c, m.christoffel b a c x * K.X x c)
        - ∑ i, ∑ j, (∑ a, (pd (m.christoffel a j i) a x - pd (m.christoffel a a i) j x
            + ∑ e, (m.christoffel a a e x * m.christoffel e j i x
              - m.christoffel a j e x * m.christoffel e a i x))) * K.X x i * K.X x j :=
    final_alg (fun c => K.X x c) (fun a b => pd (fun y => K.X y a) b x)
      (fun a b c => pd (pd (fun y => K.X y a) b) c x) (fun a b c => m.christoffel a b c x)
      (fun a b c d => pd (m.christoffel a b c) d x)
      (fun a b c => pd_pd_comm (K.smooth a) b c x)
      (fun a b c => congrFun (christoffel_symm m a b c) x)
      (fun a b c d => congrArg (fun f => pd f d x) (christoffel_symm m a b c))
      (fun a => K.geodesic x a) hgeo2
  have htrDD : trace (D * D) = ∑ a, ∑ b,
      (pd (fun y => K.X y a) b x + ∑ c, m.christoffel a b c x * K.X x c)
        * (pd (fun y => K.X y b) a x + ∑ c, m.christoffel b a c x * K.X x c) := rfl
  have hRic : m.ricciQuad x (K.X x) = ∑ i, ∑ j, (∑ a, (pd (m.christoffel a j i) a x
      - pd (m.christoffel a a i) j x
            + ∑ e, (m.christoffel a a e x * m.christoffel e j i x
              - m.christoffel a j e x * m.christoffel e a i x))) * K.X x i * K.X x j := rfl
  rw [hLHS, hF, hsh, hvo, hθ, ← htrDD, ← hRic]
  linarith [hL]

end RayBuild

open MathematicalRelativity in
theorem solution
    (m : Spacetime) (K : Congruence m) (x : Pt) :
    K.along K.expansion x
      = - (1/3 : ℝ) * (K.expansion x) ^ 2 - K.shearSq x + K.vorticitySq x
        - m.ricciQuad x (K.X x) := by
  exact RayBuild.raychaudhuri_main m K x
