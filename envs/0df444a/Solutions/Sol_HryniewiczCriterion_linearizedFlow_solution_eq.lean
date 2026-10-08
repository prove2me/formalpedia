-- Prove2me | solution 1 for HryniewiczCriterion.linearizedFlow_solution_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T17:17:41.032996+00:00
-- url     : https://prove2.me/submissions/5afbac6a-c907-4967-8490-41ce0910ed5a

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Matrix

namespace HryniewiczCriterion

/-- `e i` is the `i`-th standard basis vector of `ℝ⁴`. -/
lemma clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

/-- The linear map `L ↦ J ∇L`: `jvec L = (-L e₁, L e₀, -L e₃, L e₂)`. -/
noncomputable def jvec : (R4 →L[ℝ] ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![-(ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 1 : R4),
      -(ContinuousLinearMap.apply ℝ ℝ (Pi.single 3 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 2 1 : R4)] i

lemma jvec_apply (L : R4 →L[ℝ] ℝ) :
    jvec L = ![-L (Pi.single 1 1), L (Pi.single 0 1), -L (Pi.single 3 1), L (Pi.single 2 1)] := by
  ext i; fin_cases i <;> simp [jvec]

lemma hamiltonianVectorField_eq (H : R4 → ℝ) :
    hamiltonianVectorField H = fun y => jvec (fderiv ℝ H y) := by
  funext y; rw [jvec_apply]; rfl

lemma omega0_jvec_left (L : R4 →L[ℝ] ℝ) (q : R4) : omega0 (jvec L) q = -L q := by
  rw [clm_apply_eq_sum L q, jvec_apply]; simp [omega0]; ring

lemma omega0_jvec_right (L : R4 →L[ℝ] ℝ) (p : R4) : omega0 p (jvec L) = L p := by
  rw [clm_apply_eq_sum L p, jvec_apply]; simp [omega0] <;> ring

lemma apply_jvec_add (L M : R4 →L[ℝ] ℝ) : L (jvec M) + M (jvec L) = 0 := by
  rw [clm_apply_eq_sum L, clm_apply_eq_sum M, jvec_apply, jvec_apply]; simp; ring

lemma apply_jvec_self (L : R4 →L[ℝ] ℝ) : L (jvec L) = 0 := by
  have := apply_jvec_add L L; linarith

lemma liouvilleForm_eq (x v : R4) : liouvilleForm x v = omega0 x v / 2 := by
  simp [liouvilleForm, omega0]

lemma omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma omega0_smul_smul (u v : R4) (p q : ℝ) : omega0 (p • u) (q • v) = p * q * omega0 u v := by
  simp [omega0]; ring

/-- A symplectic pair `Z₁, Z₂` together with an `ω₀`-orthogonal symplectic pair `a, b`
spans `ℝ⁴`; every `v` that is `ω₀`-orthogonal to `a, b` lies in `span (Z₁, Z₂)`. -/
lemma eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [omega0_self, h12, h1a, h1b] at e1
    rw [omega0_antisymm Z₂ Z₁, h12, omega0_self, h2a, h2b] at e2
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, h1a, h2a, omega0_self] at e3
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, h1b, h2b,
      omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  -- pair with `a` and `b` to kill the last two coefficients
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, omega0_antisymm a b, omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, omega0_self]; ring
  rw [h1a, h2a, omega0_self, omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, omega0_lin_left, omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, omega0_antisymm, omega0_lin_left, omega0_self, omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

/-- In the situation of `eq_frame_of_omega0`, `ω₀` on two such vectors is the
determinant of their `(Z₁, Z₂)`-coordinates. -/
lemma omega0_eq_det_of_frame (Z₁ Z₂ a b v w : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0)
    (hwa : omega0 w a = 0) (hwb : omega0 w b = 0) :
    omega0 v w = omega0 v Z₂ * omega0 Z₁ w - omega0 w Z₂ * omega0 Z₁ v := by
  have hv := eq_frame_of_omega0 Z₁ Z₂ a b v h12 h1a h1b h2a h2b hab hva hvb
  have hw := eq_frame_of_omega0 Z₁ Z₂ a b w h12 h1a h1b h2a h2b hab hwa hwb
  set p := omega0 v Z₂; set q := omega0 Z₁ v
  set r := omega0 w Z₂; set s := omega0 Z₁ w
  rw [hv, hw]
  simp only [omega0] at h12 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (p * s - r * q) * h12

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

lemma contDiff_fderiv_of_smooth (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (fderiv ℝ H) :=
  hH.fderiv_right le_rfl

lemma contDiff_fderiv2_of_smooth (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ H)) :=
  (contDiff_fderiv_of_smooth hH).fderiv_right le_rfl

lemma hasFDerivAt_hvf (hH : ContDiff ℝ ∞ H) (y : R4) :
    HasFDerivAt (hamiltonianVectorField H) (jvec.comp (fderiv ℝ (fderiv ℝ H) y)) y := by
  rw [hamiltonianVectorField_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ H) y :=
    (contDiff_fderiv_of_smooth hH).differentiable (by simp) y
  exact jvec.hasFDerivAt.comp y hd.hasFDerivAt

lemma fderiv_hvf (hH : ContDiff ℝ ∞ H) (y : R4) :
    fderiv ℝ (hamiltonianVectorField H) y = jvec.comp (fderiv ℝ (fderiv ℝ H) y) :=
  (hasFDerivAt_hvf hH y).fderiv

lemma D2_symm (hH : ContDiff ℝ ∞ H) (y v w : R4) :
    fderiv ℝ (fderiv ℝ H) y v w = fderiv ℝ (fderiv ℝ H) y w v :=
  hH.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top) v w

lemma contDiff_hvf (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamiltonianVectorField H) := by
  rw [hamiltonianVectorField_eq]
  exact jvec.contDiff.comp (contDiff_fderiv_of_smooth hH)

/-- Bootstrapping: a solution of `f' = g` with `g` as smooth as `f` is `C^∞`. -/
lemma contDiff_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : ∀ n : ℕ, ContDiff ℝ n f → ContDiff ℝ n g) : ContDiff ℝ ∞ f := by
  rw [contDiff_infty]
  intro n
  induction n with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hf t).continuousAt)
  | succ n ih =>
    have hd : deriv f = g := funext fun t => (hf t).deriv
    have h := contDiff_succ_iff_deriv (𝕜 := ℝ) (f := f) (n := (n : ℕ∞ω))
    push_cast
    refine h.2 ⟨fun t => (hf t).differentiableAt, by simp, ?_⟩
    rw [hd]; exact hg n ih

lemma trajectory_contDiff (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x) :
    ContDiff ℝ ∞ x :=
  contDiff_of_hasDerivAt hx.1 fun n hn =>
    ((contDiff_hvf hH).of_le (by exact_mod_cast le_top)).comp hn

lemma linearizedFlow_contDiff (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) : ContDiff ℝ ∞ Y := by
  refine contDiff_of_hasDerivAt hY.2 fun n hn => ?_
  have hA : ContDiff ℝ ∞ fun t => fderiv ℝ (hamiltonianVectorField H) (x t) := by
    simp_rw [fderiv_hvf hH]
    exact contDiff_const.clm_comp
      ((contDiff_fderiv2_of_smooth hH).comp (trajectory_contDiff hH hx))
  exact (hA.of_le (by exact_mod_cast le_top)).clm_comp hn

lemma linearizedFlow_hasDerivAt (hH : ContDiff ℝ ∞ H) {x : ℝ → R4}
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u : R4) (t : ℝ) :
    HasDerivAt (fun t => Y t u) (jvec (fderiv ℝ (fderiv ℝ H) (x t) (Y t u))) t := by
  have h := (hY.2 t).clm_apply (hasDerivAt_const t u)
  simpa [fderiv_hvf hH] using h

/-- The linearized Hamiltonian flow is symplectic. -/
lemma omega0_linearizedFlow (hH : ContDiff ℝ ∞ H) {x : ℝ → R4}
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u v : R4) (t : ℝ) :
    omega0 (Y t u) (Y t v) = omega0 u v := by
  set g : ℝ → ℝ := fun t => omega0 (Y t u) (Y t v) with hg
  have hder : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAt hH hY u s) i
    have k := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAt hH hY v s) i
    have key := ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
      ((h 3).mul (k 2))
    have hval : omega0 (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s u))) (Y s v) +
        omega0 (Y s u) (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s v))) = 0 := by
      rw [omega0_jvec_left, omega0_jvec_right, D2_symm hH]; ring
    have key2 := key.congr_of_eventuallyEq (f₁ := g)
      (Filter.Eventually.of_forall fun r => by simp [hg, omega0])
    exact key2.congr_deriv (by rw [← hval]; simp only [omega0]; ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hg] at hc
  rw [hc, hY.1]; rfl

/-- The linearized flow preserves `dH`: it maps `T_{x(0)} S` to `T_{x(t)} S`. -/
lemma dH_linearizedFlow (hH : ContDiff ℝ ∞ H) {x : ℝ → R4} (hx : IsTrajectory H x)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (v : R4) (t : ℝ) :
    fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v := by
  set f : ℝ → ℝ := fun t => fderiv ℝ H (x t) (Y t v) with hf
  have hder : ∀ s, HasDerivAt f 0 s := by
    intro s
    have hd : DifferentiableAt ℝ (fderiv ℝ H) (x s) :=
      (contDiff_fderiv_of_smooth hH).differentiable (by simp) (x s)
    have h1 := hd.hasFDerivAt.comp_hasDerivAt s (hx.1 s)
    have h2 := h1.clm_apply (linearizedFlow_hasDerivAt hH hY v s)
    refine h2.congr_deriv ?_
    rw [hamiltonianVectorField_eq, Function.comp_apply]
    rw [D2_symm hH, add_comm]
    exact apply_jvec_add _ _
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hf] at hc
  rw [hc, hY.1]; rfl

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Pointwise frame identities -/

lemma ne_zero_of_dH_pos {y : R4} (hy : 0 < fderiv ℝ H y y) : y ≠ 0 := by
  rintro rfl; simp at hy

lemma dot4_pos {y : R4} (hy : y ≠ 0) : 0 < dot4 y y := by
  by_contra h
  push Not at h
  apply hy
  have hs : ∀ i, y i * y i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ y j * y j := fun j _ => mul_self_nonneg _
    have hsum : ∑ j, y j * y j = 0 := le_antisymm h (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  ext i; simpa using hs i

lemma euclidNorm_sq (y : R4) : euclidNorm y * euclidNorm y = dot4 y y := by
  have : 0 ≤ dot4 y y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
  exact Real.mul_self_sqrt this

lemma dH_xiFrameRaw {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y (xiFrameRaw H Q y) = 0 := by
  simp only [xiFrameRaw, map_sub, map_smul, smul_eq_mul]
  field_simp; ring

lemma omega0_xiFrameRaw_self (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y (xiFrameRaw H Q y) = 0 := by
  have := hQ y
  simp only [xiFrameRaw, omega0] at this ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

lemma omega0_quatQ1 (y : R4) : omega0 y (quatQ1 y) = 0 := by
  simp [omega0, quatQ1]; ring

lemma omega0_quatQ2 (y : R4) : omega0 y (quatQ2 y) = 0 := by
  simp [omega0, quatQ2]; ring

lemma omega0_raw21 (y : R4) :
    omega0 (xiFrameRaw H quatQ2 y) (xiFrameRaw H quatQ1 y) = dot4 y y := by
  simp [xiFrameRaw, omega0, quatQ1, quatQ2, dot4, Fin.sum_univ_four]; ring

lemma omega0_xiFrame12 {y : R4} (hy : 0 < fderiv ℝ H y y) :
    omega0 (xiFrame1 H y) (xiFrame2 H y) = 1 := by
  have hpos := dot4_pos (ne_zero_of_dH_pos hy)
  have hn := euclidNorm_sq y
  have hne : euclidNorm y ≠ 0 := by
    intro h; rw [h] at hn; linarith
  rw [xiFrame1, xiFrame2, omega0_smul_smul, omega0_raw21, ← hn]
  field_simp

lemma omega0_xiFrame_y {y : R4} (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) :
    omega0 ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) y = 0 := by
  rw [omega0_antisymm]
  simp only [omega0] at *
  have := omega0_xiFrameRaw_self (H := H) Q hQ y
  simp only [omega0] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination (-(euclidNorm y)⁻¹) * this

lemma omega0_xiFrame_X {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    omega0 ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) (hamiltonianVectorField H y) = 0 := by
  rw [omega0_antisymm, hamiltonianVectorField_eq]
  simp only
  rw [omega0_jvec_left, map_smul, dH_xiFrameRaw hy]; simp

lemma omega0_y_X (y : R4) : omega0 y (hamiltonianVectorField H y) = fderiv ℝ H y y := by
  rw [hamiltonianVectorField_eq]; exact omega0_jvec_right _ _

lemma liouville_X (y : R4) :
    liouvilleForm y (hamiltonianVectorField H y) = fderiv ℝ H y y / 2 := by
  rw [liouvilleForm_eq, omega0_y_X]

/-! ### The Reeb projection -/

lemma omega0_reeb_y {y : R4} (hy : 0 < fderiv ℝ H y y) (w : R4) :
    omega0 (reebProjection H y w) y = 0 := by
  have hl : liouvilleForm y (hamiltonianVectorField H y) ≠ 0 := by
    rw [liouville_X]; positivity
  have hlin : ∀ (u X : R4) (c : ℝ), liouvilleForm y (u - c • X) =
      liouvilleForm y u - c * liouvilleForm y X := by
    intro u X c; simp [liouvilleForm]; ring
  have : liouvilleForm y (reebProjection H y w) = 0 := by
    rw [reebProjection, hlin, div_mul_cancel₀ _ hl, sub_self]
  rw [omega0_antisymm, liouvilleForm_eq] at *
  linarith

lemma dH_reeb (y w : R4) :
    fderiv ℝ H y (reebProjection H y w) = fderiv ℝ H y w := by
  rw [reebProjection, map_sub, map_smul, hamiltonianVectorField_eq]
  simp [apply_jvec_self]

lemma omega0_X_left (y w : R4) :
    omega0 (hamiltonianVectorField H y) w = -fderiv ℝ H y w := by
  rw [hamiltonianVectorField_eq]; exact omega0_jvec_left _ _

lemma omega0_reeb_X (y w : R4) (hw : fderiv ℝ H y w = 0) :
    omega0 (reebProjection H y w) (hamiltonianVectorField H y) = 0 := by
  rw [omega0_antisymm, omega0_X_left, dH_reeb, hw]; simp

lemma omega0_reeb_reeb (y v w : R4) (hv : fderiv ℝ H y v = 0) (hw : fderiv ℝ H y w = 0) :
    omega0 (reebProjection H y v) (reebProjection H y w) = omega0 v w := by
  have h1 := omega0_X_left (H := H) y v
  have h2 := omega0_X_left (H := H) y w
  rw [hv] at h1; rw [hw] at h2
  set X := hamiltonianVectorField H y
  set a := liouvilleForm y v / liouvilleForm y X
  set b := liouvilleForm y w / liouvilleForm y X
  have hXX := omega0_self X
  have e : omega0 (v - a • X) (w - b • X) =
      omega0 v w - b * omega0 v X - a * omega0 X w + a * b * omega0 X X := by
    simp [omega0]; ring
  rw [reebProjection, reebProjection, e, h2, hXX, omega0_antisymm v X, h1]; ring

/-! ### Smoothness -/

lemma cd_omega0 {p q : ℝ → R4} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun τ => omega0 (p τ) (q τ)) := by
  have h := fun i => contDiff_pi.1 hp i
  have k := fun i => contDiff_pi.1 hq i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
    ((h 3).mul (k 2))

lemma cd_dH (hH : ContDiff ℝ ∞ H) {c v : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun τ => fderiv ℝ H (c τ) (v τ)) :=
  ((contDiff_fderiv_of_smooth hH).comp hc).clm_apply hv

lemma cd_quatQ1 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ1 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma cd_quatQ2 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ2 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

lemma cd_xiFrame (hH : ContDiff ℝ ∞ H) {c : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ (fun τ => Q (c τ))) :
    ContDiff ℝ ∞ (fun τ => (euclidNorm (c τ))⁻¹ • xiFrameRaw H Q (c τ)) := by
  have hraw : ContDiff ℝ ∞ (fun τ => xiFrameRaw H Q (c τ)) :=
    hQ.sub (((cd_dH hH hc hQ).div (cd_dH hH hc hc) fun τ => (hpos τ).ne').smul hc)
  have hdot : ContDiff ℝ ∞ (fun τ => dot4 (c τ) (c τ)) := by
    have h := fun i => contDiff_pi.1 hc i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hdne : ∀ τ, dot4 (c τ) (c τ) ≠ 0 := fun τ =>
    (dot4_pos (ne_zero_of_dH_pos (hpos τ))).ne'
  have hnorm : ContDiff ℝ ∞ (fun τ => euclidNorm (c τ)) := hdot.sqrt hdne
  have hnne : ∀ τ, euclidNorm (c τ) ≠ 0 := fun τ h => by
    have := euclidNorm_sq (c τ); rw [h] at this; exact hdne τ (by linarith)
  exact (hnorm.inv hnne).smul hraw

lemma cd_reeb (hH : ContDiff ℝ ∞ H) {c w : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun τ => reebProjection H (c τ) (w τ)) := by
  have hX : ContDiff ℝ ∞ (fun τ => hamiltonianVectorField H (c τ)) :=
    (contDiff_hvf hH).comp hc
  have hl1 : ContDiff ℝ ∞ (fun τ => liouvilleForm (c τ) (w τ)) := by
    simp only [liouvilleForm_eq]; exact (cd_omega0 hc hw).div_const 2
  have hl2 : ContDiff ℝ ∞ (fun τ => liouvilleForm (c τ) (hamiltonianVectorField H (c τ))) := by
    simp only [liouvilleForm_eq]; exact (cd_omega0 hc hX).div_const 2
  have hne : ∀ τ, liouvilleForm (c τ) (hamiltonianVectorField H (c τ)) ≠ 0 := fun τ => by
    rw [liouville_X]; exact (half_pos (hpos τ)).ne'
  exact hw.sub ((hl1.div hl2 hne).smul hX)

/-! ### Assembly -/

theorem linearizedXiPath_isSymplecticPath' (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath H P Y t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath H P Y t).det = 1) ∧
      linearizedXiPath H P Y 0 = 1 := by
  have hH := hS.1
  have hpos : ∀ t, 0 < fderiv ℝ H (P.x t) (P.x t) := fun t =>
    hS.2.2 _ (P.trajectory.2 t)
  have hx := trajectory_contDiff hH P.trajectory
  have hYc := linearizedFlow_contDiff hH P.trajectory hY
  have hx0 : 0 < fderiv ℝ H (P.x 0) (P.x 0) := hpos 0
  set E : Fin 2 → R4 := ![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] with hE
  -- frame facts at (P.x 0)
  have hE0 : ∀ j, fderiv ℝ H (P.x 0) (E j) = 0 := by
    intro j; fin_cases j <;> simp [hE, xiFrame1, xiFrame2, map_smul, dH_xiFrameRaw hx0]
  have hEl : ∀ j, liouvilleForm (P.x 0) (E j) = 0 := by
    intro j
    rw [liouvilleForm_eq, omega0_antisymm]
    fin_cases j
    · simp [hE, xiFrame1, omega0_xiFrame_y quatQ2 omega0_quatQ2]
    · simp [hE, xiFrame2, omega0_xiFrame_y quatQ1 omega0_quatQ1]
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    have hc : ContDiff ℝ ∞ (fun τ => P.x (P.T * τ)) := hx.comp (contDiff_const.mul contDiff_id)
    have hcpos : ∀ τ, 0 < fderiv ℝ H (P.x (P.T * τ)) (P.x (P.T * τ)) := fun τ => hpos _
    refine ContDiff.contDiffOn (contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_)
    have hw : ContDiff ℝ ∞ (fun τ => Y (P.T * τ) (E j)) :=
      (hYc.comp (contDiff_const.mul contDiff_id)).clm_apply contDiff_const
    have hr := cd_reeb hH hc hcpos hw
    have hZ1 := cd_xiFrame hH hc hcpos quatQ2 (cd_quatQ2 hc)
    have hZ2 := cd_xiFrame hH hc hcpos quatQ1 (cd_quatQ1 hc)
    fin_cases i
    · simpa [linearizedXiPath, xiCoords, xiFrame2, hE] using cd_omega0 hr hZ2
    · simpa [linearizedXiPath, xiCoords, xiFrame1, hE] using cd_omega0 hZ1 hr
  · -- determinant
    intro τ _
    set y := P.x (P.T * τ)
    have hy := hpos (P.T * τ)
    set w : Fin 2 → R4 := fun j => Y (P.T * τ) (E j)
    have hw : ∀ j, fderiv ℝ H y (w j) = 0 := fun j => by
      simp only [w, y]; rw [dH_linearizedFlow hH P.trajectory hY, hE0]
    set r : Fin 2 → R4 := fun j => reebProjection H y (w j)
    have hdet := omega0_eq_det_of_frame (xiFrame1 H y) (xiFrame2 H y) y
      (hamiltonianVectorField H y) (r 0) (r 1) (omega0_xiFrame12 hy)
      (omega0_xiFrame_y quatQ2 omega0_quatQ2) (omega0_xiFrame_X hy quatQ2)
      (omega0_xiFrame_y quatQ1 omega0_quatQ1) (omega0_xiFrame_X hy quatQ1)
      (by rw [omega0_y_X]; exact hy.ne')
      (omega0_reeb_y hy _) (omega0_reeb_X y _ (hw 0))
      (omega0_reeb_y hy _) (omega0_reeb_X y _ (hw 1))
    have hrr : omega0 (r 0) (r 1) = 1 := by
      simp only [r]
      rw [omega0_reeb_reeb y _ _ (hw 0) (hw 1)]
      simp only [w]
      rw [omega0_linearizedFlow hH hY]
      simp [hE, omega0_xiFrame12 hx0]
    have hm : linearizedXiPath H P Y τ = Matrix.of
        ![![omega0 (r 0) (xiFrame2 H y), omega0 (r 1) (xiFrame2 H y)],
          ![omega0 (xiFrame1 H y) (r 0), omega0 (xiFrame1 H y) (r 1)]] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hm, Matrix.det_fin_two_of]
    linarith [hdet, hrr]
  · -- initial value
    have hr : ∀ j, reebProjection H (P.x 0) (Y 0 (E j)) = E j := by
      intro j
      rw [hY.1]
      simp [reebProjection, hEl j]
    ext i j
    simp only [linearizedXiPath, Matrix.of_apply, mul_zero]
    rw [hr j]
    fin_cases i <;> fin_cases j <;>
      simp [xiCoords, hE, omega0_xiFrame12 hx0, omega0_self, Matrix.one_apply,
        omega0_antisymm (xiFrame2 H (P.x 0)) (xiFrame1 H (P.x 0))]

end HryniewiczCriterion

/-!
Local versions of `Scratch.HwzDyn` / `Scratch.HwzFin`: `H` is smooth only on an open set `U`
containing the orbit (e.g. `U = {x ≠ 0}` for a homogeneous convex model).
-/


namespace HryniewiczCriterion

variable {H : R4 → ℝ} {U : Set R4}

lemma cdOn_fderiv (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) : ContDiffOn ℝ ∞ (fderiv ℝ H) U :=
  hH.fderiv_of_isOpen hU le_rfl

lemma cdOn_fderiv2 (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) :
    ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ H)) U :=
  (cdOn_fderiv hU hH).fderiv_of_isOpen hU le_rfl

lemma hasFDerivAt_hvfOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {y : R4} (hy : y ∈ U) :
    HasFDerivAt (hamiltonianVectorField H) (jvec.comp (fderiv ℝ (fderiv ℝ H) y)) y := by
  rw [hamiltonianVectorField_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ H) y :=
    ((cdOn_fderiv hU hH).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  exact jvec.hasFDerivAt.comp y hd.hasFDerivAt

lemma fderiv_hvfOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {y : R4} (hy : y ∈ U) :
    fderiv ℝ (hamiltonianVectorField H) y = jvec.comp (fderiv ℝ (fderiv ℝ H) y) :=
  (hasFDerivAt_hvfOn hU hH hy).fderiv

lemma D2_symmOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {y : R4} (hy : y ∈ U) (v w : R4) :
    fderiv ℝ (fderiv ℝ H) y v w = fderiv ℝ (fderiv ℝ H) y w v :=
  (hH.contDiffAt (hU.mem_nhds hy)).isSymmSndFDerivAt
    (by simp; exact WithTop.coe_le_coe.2 le_top) v w

lemma cdOn_hvf (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) :
    ContDiffOn ℝ ∞ (hamiltonianVectorField H) U := by
  rw [hamiltonianVectorField_eq]
  exact jvec.contDiff.comp_contDiffOn (cdOn_fderiv hU hH)

lemma trajectory_contDiffOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hx : IsTrajectory H x) (hxU : ∀ t, x t ∈ U) : ContDiff ℝ ∞ x :=
  contDiff_of_hasDerivAt hx.1 fun n hn =>
    ((cdOn_hvf hU hH).of_le (by exact_mod_cast le_top)).comp_contDiff hn hxU

lemma linearizedFlow_contDiffOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hx : IsTrajectory H x) (hxU : ∀ t, x t ∈ U)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) : ContDiff ℝ ∞ Y := by
  refine contDiff_of_hasDerivAt hY.2 fun n hn => ?_
  have hA : ContDiff ℝ ∞ fun t => fderiv ℝ (hamiltonianVectorField H) (x t) := by
    have e : (fun t => fderiv ℝ (hamiltonianVectorField H) (x t)) =
        fun t => jvec.comp (fderiv ℝ (fderiv ℝ H) (x t)) :=
      funext fun t => fderiv_hvfOn hU hH (hxU t)
    rw [e]
    exact contDiff_const.clm_comp
      ((cdOn_fderiv2 hU hH).comp_contDiff (trajectory_contDiffOn hU hH hx hxU) hxU)
  exact (hA.of_le (by exact_mod_cast le_top)).clm_comp hn

lemma linearizedFlow_hasDerivAtOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hxU : ∀ t, x t ∈ U)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (u : R4) (t : ℝ) :
    HasDerivAt (fun t => Y t u) (jvec (fderiv ℝ (fderiv ℝ H) (x t) (Y t u))) t := by
  have h := (hY.2 t).clm_apply (hasDerivAt_const t u)
  simpa [fderiv_hvfOn hU hH (hxU t)] using h

/-- Any solution `w` of the linearized equation `w' = J D²H(x) w` pairs with `Y(t) u`
to a constant. -/
lemma omega0_flow_solution (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hxU : ∀ t, x t ∈ U) {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y)
    {w : ℝ → R4} (hw : ∀ t, HasDerivAt w (jvec (fderiv ℝ (fderiv ℝ H) (x t) (w t))) t)
    (u : R4) (t : ℝ) :
    omega0 (Y t u) (w t) = omega0 u (w 0) := by
  set g : ℝ → ℝ := fun t => omega0 (Y t u) (w t) with hg
  have hder : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h := fun i => hasDerivAt_pi.1 (linearizedFlow_hasDerivAtOn hU hH hxU hY u s) i
    have k := fun i => hasDerivAt_pi.1 (hw s) i
    have key := ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
      ((h 3).mul (k 2))
    have hval : omega0 (jvec (fderiv ℝ (fderiv ℝ H) (x s) (Y s u))) (w s) +
        omega0 (Y s u) (jvec (fderiv ℝ (fderiv ℝ H) (x s) (w s))) = 0 := by
      rw [omega0_jvec_left, omega0_jvec_right, D2_symmOn hU hH (hxU s)]; ring
    have key2 := key.congr_of_eventuallyEq (f₁ := g)
      (Filter.Eventually.of_forall fun r => by simp [hg, omega0])
    exact key2.congr_deriv (by rw [← hval]; simp only [omega0]; ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (hder s).differentiableAt)
    (fun s => (hder s).deriv) t 0
  simp only [hg] at hc
  rw [hc, hY.1]; rfl

lemma omega0_linearizedFlowOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hxU : ∀ t, x t ∈ U) {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y)
    (u v : R4) (t : ℝ) : omega0 (Y t u) (Y t v) = omega0 u v := by
  have := omega0_flow_solution hU hH hxU hY (w := fun t => Y t v)
    (linearizedFlow_hasDerivAtOn hU hH hxU hY v) u t
  rw [this, hY.1]; rfl

lemma omega0_nondeg {a b : R4} (h : ∀ u, omega0 u a = omega0 u b) : a = b := by
  have e := fun i => h (Pi.single i 1)
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3
  simp [omega0, Pi.single_apply] at e0 e1 e2 e3
  ext i; fin_cases i <;> simp <;> linarith

/-- The linearized flow is surjective (it preserves `ω₀`). -/
lemma linearizedFlow_surj (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hxU : ∀ t, x t ∈ U) {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (t : ℝ) :
    Function.Surjective (Y t) := by
  have hinj : Function.Injective (Y t) := by
    refine (injective_iff_map_eq_zero (Y t)).2 fun u hu => ?_
    refine omega0_nondeg fun v => ?_
    have := omega0_linearizedFlowOn hU hH hxU hY v u t
    rw [hu] at this
    rw [← this]; simp [omega0]
  exact LinearMap.injective_iff_surjective.1 hinj

/-- A solution of the linearized equation is `Y(t) w(0)`. -/
lemma flow_solution_eq (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hxU : ∀ t, x t ∈ U) {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y)
    {w : ℝ → R4} (hw : ∀ t, HasDerivAt w (jvec (fderiv ℝ (fderiv ℝ H) (x t) (w t))) t)
    (t : ℝ) : w t = Y t (w 0) := by
  refine omega0_nondeg fun v => ?_
  obtain ⟨u, rfl⟩ := linearizedFlow_surj hU hH hxU hY t v
  rw [omega0_flow_solution hU hH hxU hY hw, omega0_linearizedFlowOn hU hH hxU hY]

lemma dH_linearizedFlowOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {x : ℝ → R4}
    (hx : IsTrajectory H x) (hxU : ∀ t, x t ∈ U)
    {Y : ℝ → (R4 →L[ℝ] R4)} (hY : IsLinearizedFlow H x Y) (v : R4) (t : ℝ) :
    fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v := by
  have h := omega0_flow_solution hU hH hxU hY (w := fun t => hamiltonianVectorField H (x t))
    ?_ v t
  · rw [omega0_antisymm, omega0_X_left, omega0_antisymm v, omega0_X_left] at h
    simpa using h
  intro s
  exact (hasFDerivAt_hvfOn hU hH (hxU s)).comp_hasDerivAt s (hx.1 s)

/-! ### Smoothness along a curve in `U` -/

lemma cd_dHOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {c v : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hcU : ∀ τ, c τ ∈ U) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun τ => fderiv ℝ H (c τ) (v τ)) :=
  ((cdOn_fderiv hU hH).comp_contDiff hc hcU).clm_apply hv

lemma cd_xiFrameOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {c : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hcU : ∀ τ, c τ ∈ U)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ (fun τ => Q (c τ))) :
    ContDiff ℝ ∞ (fun τ => (euclidNorm (c τ))⁻¹ • xiFrameRaw H Q (c τ)) := by
  have hraw : ContDiff ℝ ∞ (fun τ => xiFrameRaw H Q (c τ)) :=
    hQ.sub (((cd_dHOn hU hH hc hcU hQ).div (cd_dHOn hU hH hc hcU hc)
      fun τ => (hpos τ).ne').smul hc)
  have hdot : ContDiff ℝ ∞ (fun τ => dot4 (c τ) (c τ)) := by
    have h := fun i => contDiff_pi.1 hc i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hdne : ∀ τ, dot4 (c τ) (c τ) ≠ 0 := fun τ =>
    (dot4_pos (ne_zero_of_dH_pos (hpos τ))).ne'
  have hnorm : ContDiff ℝ ∞ (fun τ => euclidNorm (c τ)) := hdot.sqrt hdne
  have hnne : ∀ τ, euclidNorm (c τ) ≠ 0 := fun τ h => by
    have := euclidNorm_sq (c τ); rw [h] at this; exact hdne τ (by linarith)
  exact (hnorm.inv hnne).smul hraw

lemma cd_reebOn (hU : IsOpen U) (hH : ContDiffOn ℝ ∞ H U) {c w : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hcU : ∀ τ, c τ ∈ U)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun τ => reebProjection H (c τ) (w τ)) := by
  have hX : ContDiff ℝ ∞ (fun τ => hamiltonianVectorField H (c τ)) :=
    (cdOn_hvf hU hH).comp_contDiff hc hcU
  have hl1 : ContDiff ℝ ∞ (fun τ => liouvilleForm (c τ) (w τ)) := by
    simp only [liouvilleForm_eq]; exact (cd_omega0 hc hw).div_const 2
  have hl2 : ContDiff ℝ ∞ (fun τ => liouvilleForm (c τ) (hamiltonianVectorField H (c τ))) := by
    simp only [liouvilleForm_eq]; exact (cd_omega0 hc hX).div_const 2
  have hne : ∀ τ, liouvilleForm (c τ) (hamiltonianVectorField H (c τ)) ≠ 0 := fun τ => by
    rw [liouville_X]; exact (half_pos (hpos τ)).ne'
  exact hw.sub ((hl1.div hl2 hne).smul hX)

/-- `linearizedXiPath_isSymplecticPath` with `H` smooth only on an open set around the orbit. -/
theorem linearizedXiPath_isSymplecticPathOn (H : R4 → ℝ) (U : Set R4) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (P : PeriodicOrbit H) (hxU : ∀ t, P.x t ∈ U)
    (hpos : ∀ t, 0 < fderiv ℝ H (P.x t) (P.x t))
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y) :
    ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath H P Y t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath H P Y t).det = 1) ∧
      linearizedXiPath H P Y 0 = 1 := by
  have hx := trajectory_contDiffOn hU hH P.trajectory hxU
  have hYc := linearizedFlow_contDiffOn hU hH P.trajectory hxU hY
  have hx0 : 0 < fderiv ℝ H (P.x 0) (P.x 0) := hpos 0
  set E : Fin 2 → R4 := ![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] with hE
  have hE0 : ∀ j, fderiv ℝ H (P.x 0) (E j) = 0 := by
    intro j; fin_cases j <;> simp [hE, xiFrame1, xiFrame2, map_smul, dH_xiFrameRaw hx0]
  have hEl : ∀ j, liouvilleForm (P.x 0) (E j) = 0 := by
    intro j
    rw [liouvilleForm_eq, omega0_antisymm]
    fin_cases j
    · simp [hE, xiFrame1, omega0_xiFrame_y quatQ2 omega0_quatQ2]
    · simp [hE, xiFrame2, omega0_xiFrame_y quatQ1 omega0_quatQ1]
  refine ⟨?_, ?_, ?_⟩
  · have hc : ContDiff ℝ ∞ (fun τ => P.x (P.T * τ)) := hx.comp (contDiff_const.mul contDiff_id)
    have hcU : ∀ τ, P.x (P.T * τ) ∈ U := fun τ => hxU _
    have hcpos : ∀ τ, 0 < fderiv ℝ H (P.x (P.T * τ)) (P.x (P.T * τ)) := fun τ => hpos _
    refine ContDiff.contDiffOn (contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_)
    have hw : ContDiff ℝ ∞ (fun τ => Y (P.T * τ) (E j)) :=
      (hYc.comp (contDiff_const.mul contDiff_id)).clm_apply contDiff_const
    have hr := cd_reebOn hU hH hc hcU hcpos hw
    have hZ1 := cd_xiFrameOn hU hH hc hcU hcpos quatQ2 (cd_quatQ2 hc)
    have hZ2 := cd_xiFrameOn hU hH hc hcU hcpos quatQ1 (cd_quatQ1 hc)
    fin_cases i
    · simpa [linearizedXiPath, xiCoords, xiFrame2, hE] using cd_omega0 hr hZ2
    · simpa [linearizedXiPath, xiCoords, xiFrame1, hE] using cd_omega0 hZ1 hr
  · intro τ _
    set y := P.x (P.T * τ)
    have hy := hpos (P.T * τ)
    set w : Fin 2 → R4 := fun j => Y (P.T * τ) (E j)
    have hw : ∀ j, fderiv ℝ H y (w j) = 0 := fun j => by
      simp only [w, y]; rw [dH_linearizedFlowOn hU hH P.trajectory hxU hY, hE0]
    set r : Fin 2 → R4 := fun j => reebProjection H y (w j)
    have hdet := omega0_eq_det_of_frame (xiFrame1 H y) (xiFrame2 H y) y
      (hamiltonianVectorField H y) (r 0) (r 1) (omega0_xiFrame12 hy)
      (omega0_xiFrame_y quatQ2 omega0_quatQ2) (omega0_xiFrame_X hy quatQ2)
      (omega0_xiFrame_y quatQ1 omega0_quatQ1) (omega0_xiFrame_X hy quatQ1)
      (by rw [omega0_y_X]; exact hy.ne')
      (omega0_reeb_y hy _) (omega0_reeb_X y _ (hw 0))
      (omega0_reeb_y hy _) (omega0_reeb_X y _ (hw 1))
    have hrr : omega0 (r 0) (r 1) = 1 := by
      simp only [r]
      rw [omega0_reeb_reeb y _ _ (hw 0) (hw 1)]
      simp only [w]
      rw [omega0_linearizedFlowOn hU hH hxU hY]
      simp [hE, omega0_xiFrame12 hx0]
    have hm : linearizedXiPath H P Y τ = Matrix.of
        ![![omega0 (r 0) (xiFrame2 H y), omega0 (r 1) (xiFrame2 H y)],
          ![omega0 (xiFrame1 H y) (r 0), omega0 (xiFrame1 H y) (r 1)]] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hm, Matrix.det_fin_two_of]
    linarith [hdet, hrr]
  · have hr : ∀ j, reebProjection H (P.x 0) (Y 0 (E j)) = E j := by
      intro j
      rw [hY.1]
      simp [reebProjection, hEl j]
    ext i j
    simp only [linearizedXiPath, Matrix.of_apply, mul_zero]
    rw [hr j]
    fin_cases i <;> fin_cases j <;>
      simp [xiCoords, hE, omega0_xiFrame12 hx0, omega0_self, Matrix.one_apply,
        omega0_antisymm (xiFrame2 H (P.x 0)) (xiFrame1 H (P.x 0))]

end HryniewiczCriterion

namespace HryniewiczCriterion

lemma hk_open : IsOpen {x : R4 | x ≠ 0} := isOpen_ne

/-! ### Homogeneity -/

section Homog

variable {K : R4 → ℝ} (hK : IsHomogeneousConvexModel K)
include hK

lemma hk_zero : K 0 = 0 := by
  have h := hK.2.1 2 two_pos 0
  rw [smul_zero] at h; linarith

lemma hk_diff {y : R4} (hy : y ≠ 0) : DifferentiableAt ℝ K y :=
  (hK.1.contDiffAt (hk_open.mem_nhds hy)).differentiableAt (by simp)

/-- `dK(r y) = r dK(y)`. -/
lemma hk_fderiv_smul {y : R4} (hy : y ≠ 0) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ K (r • y) = r • fderiv ℝ K y := by
  have hry : r • y ≠ 0 := smul_ne_zero hr.ne' hy
  have e : (fun z : R4 => K (r • z)) = fun z => r ^ 2 * K z :=
    funext fun z => hK.2.1 r hr z
  have h1 : HasFDerivAt (fun z : R4 => K (r • z)) ((fderiv ℝ K (r • y)).comp (r • ContinuousLinearMap.id ℝ R4)) y :=
    (hk_diff hK hry).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul r)
  have h2 : HasFDerivAt (fun z : R4 => r ^ 2 * K z) (r ^ 2 • fderiv ℝ K y) y :=
    (hk_diff hK hy).hasFDerivAt.const_mul _
  rw [e] at h1
  have := h1.unique h2
  ext v
  have hv := congrArg (fun L => L v) this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hr.ne'
  rw [hv]; ring

/-- Euler: `dK(y) y = 2 K(y)`. -/
lemma hk_euler {y : R4} (hy : y ≠ 0) : fderiv ℝ K y y = 2 * K y := by
  have h0 := (hasDerivAt_id' (1 : ℝ)).smul_const y
  rw [one_smul] at h0
  have h1 : HasDerivAt (fun s : ℝ => K (s • y)) (fderiv ℝ K y y) 1 :=
    (hk_diff hK hy).hasFDerivAt.comp_hasDerivAt_of_eq 1 h0 (one_smul ℝ y).symm
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * K y) (2 * K y) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).mul_const (K y)
  have hev : (fun s : ℝ => K (s • y)) =ᶠ[nhds 1] fun s => s ^ 2 * K y := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hK.2.1 s hs y
  exact (h1.congr_of_eventuallyEq hev.symm).unique h2

lemma hk_hvf_smul {y : R4} (hy : y ≠ 0) {r : ℝ} (hr : 0 < r) :
    hamiltonianVectorField K (r • y) = r • hamiltonianVectorField K y := by
  rw [hamiltonianVectorField_eq]; simp only
  rw [hk_fderiv_smul hK hy hr, map_smul]

/-- Euler for `X_K`: `DX_K(y) y = X_K(y)`. -/
lemma hk_euler_hvf {y : R4} (hy : y ≠ 0) :
    fderiv ℝ (hamiltonianVectorField K) y y = hamiltonianVectorField K y := by
  have hd := hasFDerivAt_hvfOn (U := {x : R4 | x ≠ 0}) hk_open hK.1 hy
  have h0 := (hasDerivAt_id' (1 : ℝ)).smul_const y
  rw [one_smul] at h0
  have h1 : HasDerivAt (fun s : ℝ => hamiltonianVectorField K (s • y))
      ((jvec.comp (fderiv ℝ (fderiv ℝ K) y)) y) 1 :=
    hd.comp_hasDerivAt_of_eq 1 h0 (one_smul ℝ y).symm
  rw [hd.fderiv]
  have h2 : HasDerivAt (fun s : ℝ => s • hamiltonianVectorField K y)
      (hamiltonianVectorField K y) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (hamiltonianVectorField K y)
  have hev : (fun s : ℝ => hamiltonianVectorField K (s • y)) =ᶠ[nhds 1]
      fun s => s • hamiltonianVectorField K y := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact hk_hvf_smul hK hy hs
  exact (h1.congr_of_eventuallyEq hev.symm).unique h2

end Homog

/-! ### Matrix algebra -/

/-- `ω₀(u, v) = uᵀ Ω v`. -/
def omegaMat : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

lemma transpose_omega_mul_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (F.transpose * omegaMat * F) i j = omega0 (fun k => F k i) (fun k => F k j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, omegaMat, omega0]; ring

lemma symplJ4_mul_omegaMat : symplJ4 * omegaMat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]

lemma omegaMat_mul_symplJ4 : omegaMat * symplJ4 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]

lemma mul_apply_eq_apply_col (f : R4 →L[ℝ] R4) (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (LinearMap.toMatrix' (f : R4 →ₗ[ℝ] R4) * F) i j = f (fun k => F k j) i := by
  have := LinearMap.toMatrix'_mulVec (f : R4 →ₗ[ℝ] R4) (fun k => F k j)
  have h2 := congrFun this i
  simp only [Matrix.mulVec, dotProduct] at h2
  rw [Matrix.mul_apply]; simpa using h2

lemma clm_apply_eq_sum' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : R4 →L[ℝ] E)
    (v : R4) : L v = ∑ n, v n • L (Pi.single n 1) := by
  have hv : v = ∑ n, v n • (Pi.single n 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

/-- The Hessian matrix `Hm k l = D²H(y)(e_l)(e_k)`. -/
noncomputable def hessMat (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun k l => B (Pi.single l 1) (Pi.single k 1)

lemma bilin_eq_sum (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) (v w : R4) :
    B v w = ∑ k, ∑ l, w k * hessMat B k l * v l := by
  rw [clm_apply_eq_sum' B v]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [clm_apply_eq_sum' (B (Pi.single l 1)) w, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [hessMat]; ring

lemma jvec_eq_mul (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) (v : R4) (k : Fin 4) :
    jvec (B v) k = ((symplJ4 * hessMat B) *ᵥ v) k := by
  rw [jvec_apply]
  have e : ∀ m, B v (Pi.single m 1) = ∑ l, hessMat B m l * v l := by
    intro m; rw [bilin_eq_sum]
    simp [Pi.single_apply]
  fin_cases k <;>
    simp [e, symplJ4, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

lemma hessMat_posDef (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) : (hessMat B).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · ext k l; simp [hessMat, hsymm]
  · have := hpos v hv
    rw [bilin_eq_sum] at this
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      using this

/-! ### The main statement -/

theorem homogeneous_frame_flow_split' (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) :
    (ContDiffOn ℝ ∞ (fun t i j => linearizedXiPath K Q Z t i j) (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (linearizedXiPath K Q Z t).det = 1) ∧
      linearizedXiPath K Q Z 0 = 1) ∧
    frameFlowMatrix K Q Z 0 = 1 ∧
    (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ, (∀ i j : Fin 4, Continuous fun t => S t i j) ∧
      (∀ t, (S t).PosDef) ∧
      ∀ t : ℝ, ∀ i j : Fin 4, HasDerivAt (fun s => frameFlowMatrix K Q Z s i j)
        ((symplJ4 * S t * frameFlowMatrix K Q Z t) i j) t) ∧
    frameFlowMatrix K Q Z Q.T = blockOne (linearizedXiPath K Q Z 1) := by
  set U : Set R4 := {x | x ≠ 0} with hUdef
  have hU : IsOpen U := hk_open
  have hH : ContDiffOn ℝ ∞ K U := hK.1
  have hK1 : ∀ t, K (Q.x t) = 1 := Q.trajectory.2
  have hxU : ∀ t, Q.x t ∈ U := fun t h => by
    have := hK1 t; rw [h, hk_zero hK] at this; norm_num at this
  have hpos : ∀ t, 0 < fderiv ℝ K (Q.x t) (Q.x t) := fun t => by
    rw [hk_euler hK (hxU t), hK1]; norm_num
  -- the orbit and `X_K` along it solve the linearized equation
  have hxsol : ∀ t, Q.x t = Z t (Q.x 0) := by
    refine flow_solution_eq hU hH hxU hZ (fun t => ?_)
    have h := Q.trajectory.1 t
    rw [← hk_euler_hvf hK (hxU t), fderiv_hvfOn hU hH (hxU t)] at h
    exact h
  have hXsol : ∀ t, hamiltonianVectorField K (Q.x t) = Z t (hamiltonianVectorField K (Q.x 0)) :=
    flow_solution_eq hU hH hxU hZ (w := fun t => hamiltonianVectorField K (Q.x t))
      (fun s => (hasFDerivAt_hvfOn hU hH (hxU s)).comp_hasDerivAt s (Q.trajectory.1 s))
  have hxT : Q.x Q.T = Q.x 0 := by simpa using Q.periodic 0
  -- the frame
  set x0 := Q.x 0
  have hx0 := hpos 0
  set X0 := hamiltonianVectorField K x0
  set c := (omega0 x0 X0)⁻¹
  have hωxX : omega0 x0 X0 = fderiv ℝ K x0 x0 := omega0_y_X x0
  set Z1 := xiFrame1 K x0
  set Z2 := xiFrame2 K x0
  have h12 : omega0 Z1 Z2 = 1 := omega0_xiFrame12 hx0
  have h1x : omega0 Z1 x0 = 0 := omega0_xiFrame_y quatQ2 omega0_quatQ2
  have h2x : omega0 Z2 x0 = 0 := omega0_xiFrame_y quatQ1 omega0_quatQ1
  have h1X : omega0 Z1 X0 = 0 := omega0_xiFrame_X hx0 quatQ2
  have h2X : omega0 Z2 X0 = 0 := omega0_xiFrame_X hx0 quatQ1
  have hxX0 : omega0 x0 X0 ≠ 0 := by rw [hωxX]; exact hx0.ne'
  set F := homogFrame K x0 with hFdef
  have hcol : ∀ j, (fun k => F k j) = ![x0, c • X0, Z1, Z2] j := fun j => rfl
  have hFent : ∀ i m, F i m = ![x0, c • X0, Z1, Z2] m i := fun _ _ => rfl
  have hsr : ∀ (u v : R4) (a : ℝ), omega0 u (a • v) = a * omega0 u v := by
    intros; simp [omega0]; ring
  have hsl : ∀ (u v : R4) (a : ℝ), omega0 (a • u) v = a * omega0 u v := by
    intros; simp [omega0]; ring
  have p01 : omega0 x0 (c • X0) = 1 := by rw [hsr]; exact inv_mul_cancel₀ hxX0
  have p10 : omega0 (c • X0) x0 = -1 := by rw [omega0_antisymm, p01]
  have p21 : omega0 Z1 (c • X0) = 0 := by rw [hsr, h1X, mul_zero]
  have p31 : omega0 Z2 (c • X0) = 0 := by rw [hsr, h2X, mul_zero]
  have p12 : omega0 (c • X0) Z1 = 0 := by rw [omega0_antisymm, p21, neg_zero]
  have p13 : omega0 (c • X0) Z2 = 0 := by rw [omega0_antisymm, p31, neg_zero]
  have p02 : omega0 x0 Z1 = 0 := by rw [omega0_antisymm, h1x, neg_zero]
  have p03 : omega0 x0 Z2 = 0 := by rw [omega0_antisymm, h2x, neg_zero]
  have p32 : omega0 Z2 Z1 = -1 := by rw [omega0_antisymm, h12]
  have hFF : F.transpose * omegaMat * F = omegaMat := by
    ext i j
    rw [transpose_omega_mul_apply, hcol, hcol]
    fin_cases i <;> fin_cases j <;>
      simp [omegaMat, omega0_self, p01, p10, p21, p31, p12, p13, p02, p03, p32, h12, h1x, h2x]
  set G := symplJ4 * F.transpose * omegaMat with hG
  have hGF : G * F = 1 := by
    rw [hG, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc F.transpose, hFF,
      symplJ4_mul_omegaMat]
  have hFinv : F⁻¹ = G := Matrix.inv_eq_left_inv hGF
  have hFG : F * G = 1 := mul_eq_one_comm.1 hGF
  have hFiJ : F⁻¹ * symplJ4 = symplJ4 * F.transpose := by
    rw [hFinv, hG, Matrix.mul_assoc, omegaMat_mul_symplJ4, Matrix.mul_one]
  have hframe : ∀ t, frameFlowMatrix K Q Z t =
      F⁻¹ * LinearMap.toMatrix' (Z t : R4 →ₗ[ℝ] R4) * F := fun t => rfl
  refine ⟨linearizedXiPath_isSymplecticPathOn K U hU hH Q hxU hpos Z hZ, ?_, ?_, ?_⟩
  · -- initial value
    rw [hframe, hZ.1]
    have : ((ContinuousLinearMap.id ℝ R4 : R4 →L[ℝ] R4) : R4 →ₗ[ℝ] R4) = LinearMap.id := rfl
    rw [this, LinearMap.toMatrix'_id, Matrix.mul_one, hFinv, hGF]
  · -- the ODE
    set Hm : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t => hessMat (fderiv ℝ (fderiv ℝ K) (Q.x t))
    refine ⟨fun t => F.transpose * Hm t * F, ?_, ?_, ?_⟩
    · have hD := ((cdOn_fderiv2 hU hH).comp_contDiff
        (trajectory_contDiffOn hU hH Q.trajectory hxU) hxU).continuous
      have hHm : ∀ k l, Continuous fun t => Hm t k l := fun k l =>
        (hD.clm_apply continuous_const).clm_apply continuous_const
      intro i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      fun_prop
    · intro t
      have hy : K (Q.x t) = 1 := hK1 t
      have hPD := hessMat_posDef (fderiv ℝ (fderiv ℝ K) (Q.x t))
        (D2_symmOn hU hH (hxU t)) (hK.2.2.2 _ hy)
      have hinj : Function.Injective F.mulVec := by
        intro v w hvw
        have := congrArg (fun u => G.mulVec u) hvw
        simpa [Matrix.mulVec_mulVec, hGF] using this
      have := hPD.conjTranspose_mul_mul_same hinj
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    · intro t i j
      set M : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun s => LinearMap.toMatrix' (Z s : R4 →ₗ[ℝ] R4)
      have hMd : ∀ k l, HasDerivAt (fun s => M s k l)
          ((symplJ4 * Hm t * M t) k l) t := by
        intro k l
        have h := hasDerivAt_pi.1 (linearizedFlow_hasDerivAtOn hU hH hxU hZ (Pi.single l 1) t) k
        have e : jvec (fderiv ℝ (fderiv ℝ K) (Q.x t) (Z t (Pi.single l 1))) k =
            (symplJ4 * Hm t * M t) k l := by
          rw [jvec_eq_mul]
          simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Hm, M,
            LinearMap.toMatrix'_apply]
          rfl
        simp only [M, LinearMap.toMatrix'_apply]
        rw [← e]; exact h
      have hder : HasDerivAt (fun s => (F⁻¹ * M s * F) i j)
          ((F⁻¹ * (symplJ4 * Hm t * M t) * F) i j) t := by
        simp only [Matrix.mul_apply]
        exact HasDerivAt.fun_sum fun l _ =>
          (HasDerivAt.fun_sum fun k _ => (hMd k l).const_mul (F⁻¹ i k)).mul_const (F l j)
      have hFG' : F * F⁻¹ = 1 := by rw [hFinv]; exact hFG
      have hid : symplJ4 * (F.transpose * Hm t * F) * (F⁻¹ * M t * F) =
          F⁻¹ * (symplJ4 * Hm t * M t) * F := by
        calc symplJ4 * (F.transpose * Hm t * F) * (F⁻¹ * M t * F)
            = symplJ4 * F.transpose * Hm t * (F * F⁻¹) * M t * F := by
              simp only [Matrix.mul_assoc]
          _ = (F⁻¹ * symplJ4) * Hm t * M t * F := by rw [hFG', Matrix.mul_one, hFiJ]
          _ = F⁻¹ * (symplJ4 * Hm t * M t) * F := by simp only [Matrix.mul_assoc]
      rw [← hid] at hder
      exact hder
  · -- the splitting after one period
    set φ1 := linearizedXiPath K Q Z 1
    have hZx : Z Q.T x0 = x0 := by rw [← hxsol, hxT]
    have hZX : Z Q.T X0 = X0 := by rw [← hXsol, hxT]
    have hcolT : ∀ j : Fin 2, Z Q.T (![Z1, Z2] j) =
        φ1 0 j • Z1 + φ1 1 j • Z2 := by
      intro j
      set v := Z Q.T (![Z1, Z2] j)
      have hvx : omega0 v x0 = 0 := by
        rw [← hZx, omega0_linearizedFlowOn hU hH hxU hZ]
        fin_cases j <;> simp [h1x, h2x]
      have hvX : omega0 v X0 = 0 := by
        rw [← hZX, omega0_linearizedFlowOn hU hH hxU hZ]
        fin_cases j <;> simp [h1X, h2X]
      have hreeb : reebProjection K x0 v = v := by
        have : liouvilleForm x0 v = 0 := by
          rw [liouvilleForm_eq, omega0_antisymm, hvx]; simp
        simp [reebProjection, this]
      have hφ : ∀ i, φ1 i j = xiCoords K x0 v i := by
        intro i
        rw [← hreeb]
        simp only [φ1, linearizedXiPath, Matrix.of_apply, mul_one]
        rw [hxT]
      rw [hφ, hφ]
      exact eq_frame_of_omega0 Z1 Z2 x0 X0 v h12 h1x h1X h2x h2X hxX0 hvx hvX
    have hMF : LinearMap.toMatrix' (Z Q.T : R4 →ₗ[ℝ] R4) * F = F * blockOne φ1 := by
      ext i j
      rw [mul_apply_eq_apply_col, hcol, Matrix.mul_apply]
      have hc0 := hcolT 0
      have hc1 := hcolT 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc0 hc1
      fin_cases j <;>
        simp [hZx, hZX, hc0, hc1, blockOne, Fin.sum_univ_four, hFent, map_smul] <;> ring
    rw [hframe, Matrix.mul_assoc, hMF, ← Matrix.mul_assoc, hFinv, hGF, Matrix.one_mul]

end HryniewiczCriterion

namespace HryniewiczCriterion

theorem linearizedFlow_solution_eq' (H : R4 → ℝ) (U : Set R4) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (x : ℝ → R4) (hxU : ∀ t, x t ∈ U)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (w : ℝ → R4)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (hamiltonianVectorField H) (x t) (w t)) t) (t : ℝ) :
    w t = Y t (w 0) := by
  refine flow_solution_eq hU hH hxU hY (fun s => ?_) t
  have h := hw s
  rw [fderiv_hvfOn hU hH (hxU s)] at h
  exact h

theorem homogeneousConvexModel_euler' (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (y : R4) (hy : y ≠ 0) :
    fderiv ℝ K y y = 2 * K y ∧
      fderiv ℝ (hamiltonianVectorField K) y y = hamiltonianVectorField K y :=
  ⟨hk_euler hK hy, hk_euler_hvf hK hy⟩

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (U : Set R4) (hU : IsOpen U)
    (hH : ContDiffOn ℝ ∞ H U) (x : ℝ → R4) (hxU : ∀ t, x t ∈ U)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (w : ℝ → R4)
    (hw : ∀ t, HasDerivAt w (fderiv ℝ (hamiltonianVectorField H) (x t) (w t)) t) (t : ℝ) :
    w t = Y t (w 0) :=
  linearizedFlow_solution_eq' H U hU hH x hxU Y hY w hw t
