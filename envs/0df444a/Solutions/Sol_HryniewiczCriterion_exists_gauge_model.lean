-- Prove2me | solution 1 for HryniewiczCriterion.exists_gauge_model
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:01:48.07927+00:00
-- url     : https://prove2.me/submissions/fb6693bc-6d78-4930-9fac-83fda9eefcd0

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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Matrix
open scoped ContDiff Topology
open Filter
open Filter Set

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

/-!
Leaf A, part 1: the square of the Minkowski gauge of a strictly star-shaped level (HWZ (3.32)).

`radial H u` is the radius where the ray through `u` crosses `S = H⁻¹(1)`; it is smooth on
`u ≠ 0` by the implicit function theorem. `gaugeSq H u = radial H u ^ (-2)` is the square of the
Minkowski gauge of the domain bounded by `S`. On `S` its differential is `(2 / dH(x) x) dH(x)`,
and its Hessian is positive definite when the Hessian of `H` is.
-/


namespace HryniewiczCriterion

variable {H : R4 → ℝ}

open Classical in
/-- The crossing radius of the ray through `u` with `S = H⁻¹(1)`. -/
noncomputable def radial (H : R4 → ℝ) (u : R4) : ℝ :=
  if h : ∃ r : ℝ, 0 < r ∧ H (r • u) = 1 then Classical.choose h else 1

/-- The square of the Minkowski gauge: `gaugeSq H u = radial H u ^ (-2)`, `gaugeSq H 0 = 0`. -/
noncomputable def gaugeSq (H : R4 → ℝ) (x : R4) : ℝ :=
  if x = 0 then 0 else (radial H x)⁻¹ ^ 2

/-- `dK(y) = gaugeCoef H y • dH(radial H y • y)`. -/
noncomputable def gaugeCoef (H : R4 → ℝ) (y : R4) : ℝ :=
  2 / (radial H y * fderiv ℝ H (radial H y • y) (radial H y • y))

lemma gaugeSq_of_ne {x : R4} (hx : x ≠ 0) : gaugeSq H x = (radial H x)⁻¹ ^ 2 := if_neg hx

lemma gaugeSq_eventually {x : R4} (hx : x ≠ 0) :
    gaugeSq H =ᶠ[𝓝 x] fun y => (radial H y)⁻¹ ^ 2 := by
  filter_upwards [eventually_ne_nhds hx] with y hy using gaugeSq_of_ne hy

/-! ### Homogeneous functions (only smoothness and homogeneity are used) -/

section Homog

variable {K : R4 → ℝ} (h1 : ContDiffOn ℝ ∞ K {x | x ≠ 0})
  (h2 : ∀ r : ℝ, 0 < r → ∀ x : R4, K (r • x) = r ^ 2 * K x)
include h1 h2

lemma homog_fderiv_smul {y : R4} (hy : y ≠ 0) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ K (r • y) = r • fderiv ℝ K y := by
  have hdiff : ∀ {z : R4}, z ≠ 0 → DifferentiableAt ℝ K z := fun hz =>
    (h1.contDiffAt (hk_open.mem_nhds hz)).differentiableAt (by simp)
  have hry : r • y ≠ 0 := smul_ne_zero hr.ne' hy
  have e : (fun z : R4 => K (r • z)) = fun z => r ^ 2 * K z :=
    funext fun z => h2 r hr z
  have k1 : HasFDerivAt (fun z : R4 => K (r • z))
      ((fderiv ℝ K (r • y)).comp (r • ContinuousLinearMap.id ℝ R4)) y :=
    (hdiff hry).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul r)
  have k2 : HasFDerivAt (fun z : R4 => r ^ 2 * K z) (r ^ 2 • fderiv ℝ K y) y :=
    (hdiff hy).hasFDerivAt.const_mul _
  rw [e] at k1
  have := k1.unique k2
  ext v
  have hv := congrArg (fun L => L v) this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hr.ne'
  rw [hv]; ring

/-- Euler for the differential: `D²K(y) y = dK(y)`. -/
lemma homog_hess_euler {y : R4} (hy : y ≠ 0) :
    fderiv ℝ (fderiv ℝ K) y y = fderiv ℝ K y := by
  have hd : HasFDerivAt (fderiv ℝ K) (fderiv ℝ (fderiv ℝ K) y) y :=
    (((cdOn_fderiv hk_open h1).contDiffAt (hk_open.mem_nhds hy)).differentiableAt
      (by simp)).hasFDerivAt
  have h0 := (hasDerivAt_id' (1 : ℝ)).smul_const y
  rw [one_smul] at h0
  have hc : HasDerivAt (fun s : ℝ => fderiv ℝ K (s • y)) (fderiv ℝ (fderiv ℝ K) y y) 1 :=
    hd.comp_hasDerivAt_of_eq 1 h0 (one_smul ℝ y).symm
  have h2' : HasDerivAt (fun s : ℝ => s • fderiv ℝ K y) (fderiv ℝ K y) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (fderiv ℝ K y)
  have hev : (fun s : ℝ => fderiv ℝ K (s • y)) =ᶠ[𝓝 1] fun s => s • fderiv ℝ K y := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact homog_fderiv_smul h1 h2 hy hs
  exact (hc.congr_of_eventuallyEq hev.symm).unique h2'

end Homog

/-! ### The gauge -/

section Gauge

variable (hS : IsStrictlyStarShapedLevel H)
include hS

lemma radial_spec {u : R4} (hu : u ≠ 0) : 0 < radial H u ∧ H (radial H u • u) = 1 := by
  have h : ∃ r : ℝ, 0 < r ∧ H (r • u) = 1 := (hS.2.1 u hu).exists
  rw [radial, dif_pos h]; exact Classical.choose_spec h

lemma radial_unique {u : R4} (hu : u ≠ 0) {r : ℝ} (hr : 0 < r) (h1 : H (r • u) = 1) :
    radial H u = r :=
  (hS.2.1 u hu).unique (radial_spec hS hu) ⟨hr, h1⟩

lemma ne_zero_of_level {x : R4} (hx : H x = 1) : x ≠ 0 := by
  rintro rfl; have := hS.2.2 0 hx; simp at this

lemma radial_of_level {x : R4} (hx : H x = 1) : radial H x = 1 :=
  radial_unique hS (ne_zero_of_level hS hx) one_pos (by rwa [one_smul])

lemma radial_smul {x : R4} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    radial H (t • x) = t⁻¹ * radial H x := by
  obtain ⟨hr, h1⟩ := radial_spec hS hx
  refine radial_unique hS (smul_ne_zero ht.ne' hx) (mul_pos (inv_pos.2 ht) hr) ?_
  have e : (t⁻¹ * radial H x) * t = radial H x := by field_simp
  rw [smul_smul, e]; exact h1

/-- Implicit function theorem for `H(r • x) = 1`: the crossing radius is smooth. -/
lemma radial_contDiffAt {x₀ : R4} (hx₀ : x₀ ≠ 0) : ContDiffAt ℝ ∞ (radial H) x₀ := by
  obtain ⟨hr0, h1⟩ := radial_spec hS hx₀
  set r₀ := radial H x₀ with hr₀
  let f : R4 × ℝ → ℝ := fun p => H (p.2 • p.1)
  have hfc : ContDiff ℝ ∞ f := hS.1.comp (contDiff_snd.smul contDiff_fst)
  have hsm : HasFDerivAt (fun p : R4 × ℝ => p.2 • p.1)
      (r₀ • ContinuousLinearMap.fst ℝ R4 ℝ + (ContinuousLinearMap.snd ℝ R4 ℝ).smulRight x₀)
      (x₀, r₀) := by
    have h := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((x₀, r₀) : R4 × ℝ))).smul
      (hasFDerivAt_fst (𝕜 := ℝ) (p := ((x₀, r₀) : R4 × ℝ)))
    exact h
  have hfd : HasFDerivAt f ((fderiv ℝ H (r₀ • x₀)).comp
      (r₀ • ContinuousLinearMap.fst ℝ R4 ℝ + (ContinuousLinearMap.snd ℝ R4 ℝ).smulRight x₀))
      (x₀, r₀) :=
    (hS.1.differentiable (by simp) _).hasFDerivAt.comp (x₀, r₀) hsm
  set d := fderiv ℝ H (r₀ • x₀) x₀ with hd
  have hdpos : 0 < d := by
    have := hS.2.2 _ h1
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr0.le
  set L := fderiv ℝ f (x₀, r₀) ∘L ContinuousLinearMap.inr ℝ R4 ℝ with hLdef
  have hL : ∀ s : ℝ, L s = s * d := by
    intro s
    rw [hLdef, ContinuousLinearMap.comp_apply, hfd.fderiv]
    simp [hd, map_smul]
  have hinv : L.IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := d⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, hL]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        mul_one]
      field_simp
    · apply ContinuousLinearMap.ext_ring
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, hL, one_mul]
      field_simp
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have cdf : ContDiffAt ℝ ∞ f (x₀, r₀) := hfc.contDiffAt
  have hψ0 : cdf.implicitFunction pn hinv x₀ = r₀ := cdf.implicitFunction_apply_self pn hinv
  have hψc : ContDiffAt ℝ ∞ (cdf.implicitFunction pn hinv) x₀ :=
    cdf.contDiffAt_implicitFunction pn hinv
  have heq := cdf.eventually_apply_implicitFunction pn hinv
  have hpos : ∀ᶠ x in 𝓝 x₀, 0 < cdf.implicitFunction pn hinv x :=
    hψc.continuousAt.eventually (lt_mem_nhds (by rw [hψ0]; exact hr0))
  have hev : radial H =ᶠ[𝓝 x₀] cdf.implicitFunction pn hinv := by
    filter_upwards [heq, hpos, eventually_ne_nhds hx₀] with x h1x h2x h3x
    refine radial_unique hS h3x h2x ?_
    have e1 : f (x₀, r₀) = 1 := h1
    have e2 := h1x
    rw [e1] at e2
    exact e2
  exact hψc.congr_of_eventuallyEq hev

lemma radial_hasFDerivAt {y : R4} (hy : y ≠ 0) :
    HasFDerivAt (radial H) (fderiv ℝ (radial H) y) y :=
  ((radial_contDiffAt hS hy).differentiableAt (by simp)).hasFDerivAt

/-- Differentiating `H(radial H y • y) = 1`. -/
lemma radial_fderiv_identity {y : R4} (hy : y ≠ 0) (v : R4) :
    radial H y * fderiv ℝ H (radial H y • y) v +
      fderiv ℝ (radial H) y v * fderiv ℝ H (radial H y • y) y = 0 := by
  have hg : HasFDerivAt (fun z => radial H z • z)
      (radial H y • ContinuousLinearMap.id ℝ R4 + (fderiv ℝ (radial H) y).smulRight y) y := by
    have h := (radial_hasFDerivAt hS hy).smul (hasFDerivAt_id y); exact h
  have hc := HasFDerivAt.comp (f := fun z => radial H z • z) y
    (hS.1.differentiable (by simp) (radial H y • y)).hasFDerivAt hg
  have hc1 : HasFDerivAt (fun z => H (radial H z • z)) (0 : R4 →L[ℝ] ℝ) y := by
    refine (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hy] with z hz
    exact (radial_spec hS hz).2
  have := congrArg (fun L => L v) (hc.unique hc1)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul,
    ContinuousLinearMap.zero_apply, id] at this
  exact this

lemma gaugeSq_contDiffAt {x : R4} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (gaugeSq H) x :=
  (((radial_contDiffAt hS hx).inv (radial_spec hS hx).1.ne').pow 2).congr_of_eventuallyEq
    (gaugeSq_eventually hx)

lemma gaugeSq_contDiffOn : ContDiffOn ℝ ∞ (gaugeSq H) {x | x ≠ 0} :=
  fun _ hx => (gaugeSq_contDiffAt hS hx).contDiffWithinAt

lemma gaugeSq_smul (t : ℝ) (ht : 0 < t) (x : R4) : gaugeSq H (t • x) = t ^ 2 * gaugeSq H x := by
  by_cases hx : x = 0
  · simp [hx, gaugeSq]
  rw [gaugeSq_of_ne (smul_ne_zero ht.ne' hx), gaugeSq_of_ne hx, radial_smul hS hx ht,
    mul_inv, inv_inv]
  ring

lemma gaugeSq_eq_one_iff (x : R4) : gaugeSq H x = 1 ↔ H x = 1 := by
  by_cases hx : x = 0
  · subst hx
    simp only [gaugeSq, if_true]
    constructor
    · intro h; norm_num at h
    · intro h; exact absurd rfl (ne_zero_of_level hS h)
  obtain ⟨hr0, h1⟩ := radial_spec hS hx
  rw [gaugeSq_of_ne hx]
  constructor
  · intro h
    have hi : (radial H x)⁻¹ = 1 := by
      have := inv_pos.2 hr0
      nlinarith [sq_nonneg ((radial H x)⁻¹ - 1)]
    rw [inv_eq_one] at hi
    rw [hi, one_smul] at h1; exact h1
  · intro h; rw [radial_of_level hS h]; norm_num

lemma gaugeCoef_contDiffAt {y : R4} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (gaugeCoef H) y := by
  obtain ⟨hr0, h1⟩ := radial_spec hS hy
  have hr := radial_contDiffAt hS hy
  have hg : ContDiffAt ℝ ∞ (fun z => radial H z • z) y := hr.smul contDiffAt_id
  have hm : ContDiffAt ℝ ∞ (fun z => fderiv ℝ H (radial H z • z) (radial H z • z)) y :=
    ((contDiff_fderiv_of_smooth hS.1).contDiffAt.comp y hg).clm_apply hg
  exact contDiffAt_const.div (hr.mul hm) (mul_ne_zero hr0.ne' (hS.2.2 _ h1).ne')

/-- The differential of the gauge model off the origin. -/
lemma hasFDerivAt_gaugeSq {y : R4} (hy : y ≠ 0) :
    HasFDerivAt (gaugeSq H) (gaugeCoef H y • fderiv ℝ H (radial H y • y)) y := by
  obtain ⟨hr0, h1⟩ := radial_spec hS hy
  have hr := radial_hasFDerivAt hS hy
  have hinv := (hasDerivAt_inv hr0.ne').comp_hasFDerivAt y hr
  have hsq := hinv.pow 2
  refine (hsq.congr_of_eventuallyEq (gaugeSq_eventually hy)).congr_fderiv ?_
  ext v
  have hid := radial_fderiv_identity hS hy v
  have hB : 0 < fderiv ℝ H (radial H y • y) y := by
    have := hS.2.2 _ h1
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr0.le
  have hdr : fderiv ℝ (radial H) y v =
      -(radial H y * fderiv ℝ H (radial H y • y) v) / fderiv ℝ H (radial H y • y) y := by
    field_simp; linarith [hid]
  have hrne := hr0.ne'
  simp only [gaugeCoef, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, Function.comp_apply,
    nsmul_eq_mul, Nat.cast_ofNat, hdr]
  field_simp
  ring_nf
  rw [mul_inv_cancel₀ hrne, one_mul]

lemma fderiv_gaugeSq_of_level {x : R4} (hx : H x = 1) :
    fderiv ℝ (gaugeSq H) x = (2 / fderiv ℝ H x x) • fderiv ℝ H x := by
  rw [(hasFDerivAt_gaugeSq hS (ne_zero_of_level hS hx)).fderiv, gaugeCoef,
    radial_of_level hS hx, one_smul, one_mul]

lemma gaugeCoef_of_level {x : R4} (hx : H x = 1) :
    gaugeCoef H x = 2 / fderiv ℝ H x x := by
  rw [gaugeCoef, radial_of_level hS hx, one_smul, one_mul]

/-- Second differential of the gauge model along tangent vectors of `S`. -/
lemma fderiv2_gaugeSq_tangent {x : R4} (hx : H x = 1) {w : R4} (hw : fderiv ℝ H x w = 0) :
    fderiv ℝ (fderiv ℝ (gaugeSq H)) x w =
      fderiv ℝ (gaugeCoef H) x w • fderiv ℝ H x +
        gaugeCoef H x • fderiv ℝ (fderiv ℝ H) x w := by
  have hx0 := ne_zero_of_level hS hx
  have hr1 := radial_of_level hS hx
  have hg : HasFDerivAt (fun z => radial H z • z)
      (radial H x • ContinuousLinearMap.id ℝ R4 + (fderiv ℝ (radial H) x).smulRight x) x := by
    have h := (radial_hasFDerivAt hS hx0).smul (hasFDerivAt_id x); exact h
  have hd2 : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) (radial H x • x))
      (radial H x • x) :=
    ((contDiff_fderiv_of_smooth hS.1).differentiable (by simp) _).hasFDerivAt
  have hdHg := HasFDerivAt.comp (f := fun z => radial H z • z) x hd2 hg
  have hc : HasFDerivAt (gaugeCoef H) (fderiv ℝ (gaugeCoef H) x) x :=
    ((gaugeCoef_contDiffAt hS hx0).differentiableAt (by simp)).hasFDerivAt
  have hΦ := hc.smul hdHg
  have hev : fderiv ℝ (gaugeSq H) =ᶠ[𝓝 x]
      fun y => gaugeCoef H y • fderiv ℝ H (radial H y • y) := by
    filter_upwards [eventually_ne_nhds hx0] with y hy using (hasFDerivAt_gaugeSq hS hy).fderiv
  rw [(hΦ.congr_of_eventuallyEq hev).fderiv]
  have hid := radial_fderiv_identity hS hx0 w
  rw [hr1, one_smul, hw] at hid
  have hm := hS.2.2 x hx
  have hdr : fderiv ℝ (radial H) x w = 0 := by
    have : fderiv ℝ (radial H) x w * fderiv ℝ H x x = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, Function.comp_apply, Pi.smul_apply, id, hr1, one_smul, hdr,
    zero_smul, add_zero]
  rw [add_comm]

/-- The Hessian of the gauge model is positive definite on `S`. -/
lemma gaugeSq_hess_pos
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v)
    {x : R4} (hx : H x = 1) {v : R4} (hv : v ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (gaugeSq H)) x v v := by
  have hx0 := ne_zero_of_level hS hx
  have h1 := gaugeSq_contDiffOn hS
  have h2 := fun r hr y => gaugeSq_smul hS r hr y
  have hm : 0 < fderiv ℝ H x x := hS.2.2 x hx
  set a := fderiv ℝ H x v / fderiv ℝ H x x with ha
  set w := v - a • x with hwdef
  have hw : fderiv ℝ H x w = 0 := by
    rw [hwdef, map_sub, map_smul, smul_eq_mul, ha]; field_simp; ring
  have hvw : v = a • x + w := by rw [hwdef]; abel
  have hBx : fderiv ℝ (fderiv ℝ (gaugeSq H)) x x = fderiv ℝ (gaugeSq H) x :=
    homog_hess_euler h1 h2 hx0
  have hdK := fderiv_gaugeSq_of_level hS hx
  have hBxw : fderiv ℝ (fderiv ℝ (gaugeSq H)) x x w = 0 := by
    rw [hBx, hdK]; simp [hw]
  have hBxx : fderiv ℝ (fderiv ℝ (gaugeSq H)) x x x = 2 := by
    rw [hBx, hdK, ContinuousLinearMap.smul_apply, smul_eq_mul]; field_simp
  have hBwx : fderiv ℝ (fderiv ℝ (gaugeSq H)) x w x = 0 := by
    rw [D2_symmOn hk_open h1 hx0 w x]; exact hBxw
  have hBww : fderiv ℝ (fderiv ℝ (gaugeSq H)) x w w =
      2 / fderiv ℝ H x x * fderiv ℝ (fderiv ℝ H) x w w := by
    rw [fderiv2_gaugeSq_tangent hS hx hw, gaugeCoef_of_level hS hx]
    simp [hw]
  have hexp : fderiv ℝ (fderiv ℝ (gaugeSq H)) x v v =
      a ^ 2 * 2 + 2 / fderiv ℝ H x x * fderiv ℝ (fderiv ℝ H) x w w := by
    rw [hvw]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hBxx, hBxw, hBwx, hBww]
    ring
  rw [hexp]
  by_cases hw0 : w = 0
  · have ha0 : a ≠ 0 := by
      intro h0; apply hv; rw [hvw, h0, hw0]; simp
    rw [hw0]; simp only [map_zero, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
    positivity
  · have := hpos x hx w hw0
    positivity

/-- A1 + A2: the gauge model is a homogeneous convex model with the same unit level. -/
theorem gaugeSq_model
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v) :
    IsHomogeneousConvexModel (gaugeSq H) := by
  refine ⟨gaugeSq_contDiffOn hS, fun r hr x => gaugeSq_smul hS r hr x, fun x hx => ?_,
    fun x hx v hv => ?_⟩
  · rw [gaugeSq_of_ne hx]; exact pow_pos (inv_pos.2 (radial_spec hS hx).1) 2
  · rw [gaugeSq_eq_one_iff hS] at hx
    exact gaugeSq_hess_pos hS hpos hx hv

lemma gaugeSq_energySurface : energySurface (gaugeSq H) = energySurface H := by
  ext x; simp only [energySurface, Set.mem_setOf_eq, gaugeSq_eq_one_iff hS]

end Gauge

end HryniewiczCriterion

/-!
Leaf A, part 2: generic tools.

* `windingInterval_comp_reparam`: the winding interval is invariant under a reparametrization of
  `[0, 1]` that fixes both ends and has a continuous inverse.
* `exists_time_change`: for a continuous positive periodic `m`, the inverse `σ` of
  `τ(s) = ∫₀ˢ m` is a strictly increasing `C¹` time change with `σ' = 1 / m(σ)` and
  `σ(t + τ(T)) = σ(t) + T`.
* transfer lemmas for a defining function whose differential is a positive multiple of `dH`.
-/


namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Reparametrization invariance of the winding interval -/

lemma windingInterval_congr {φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, φ t = φ' t) : windingInterval φ = windingInterval φ' := by
  have key : ∀ {φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ}, (∀ t ∈ Icc (0 : ℝ) 1, φ t = φ' t) →
      windingInterval φ ⊆ windingInterval φ' := by
    intro φ φ' h
    rintro d ⟨s, hs, θ, ⟨hc, h0, hθ⟩, rfl⟩
    exact ⟨s, hs, θ, ⟨hc, h0, fun t ht => (h t ht) ▸ hθ t ht⟩, rfl⟩
  exact subset_antisymm (key h) (key fun t ht => (h t ht).symm)

lemma windingInterval_subset_comp {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {ψ : ℝ → ℝ}
    (hψc : ContinuousOn ψ (Icc 0 1)) (hψm : MapsTo ψ (Icc 0 1) (Icc 0 1))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 1) :
    windingInterval φ ⊆ windingInterval (fun t => φ (ψ t)) := by
  rintro d ⟨s, hs, θ, ⟨hc, hθ0, hθ⟩, rfl⟩
  refine ⟨s, hs, fun t => θ (ψ t), ⟨hc.comp hψc hψm, by simp only [h0, hθ0],
    fun t ht => hθ (ψ t) (hψm ht)⟩, ?_⟩
  simp only [h1]

/-- The winding interval does not see a reparametrization `ψ` of `[0, 1]` fixing `0` and `1`
with a continuous inverse `χ`. -/
theorem windingInterval_comp_reparam {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {ψ χ : ℝ → ℝ}
    (hψc : ContinuousOn ψ (Icc 0 1)) (hψm : MapsTo ψ (Icc 0 1) (Icc 0 1))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 1)
    (hχc : ContinuousOn χ (Icc 0 1)) (hχm : MapsTo χ (Icc 0 1) (Icc 0 1))
    (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 1) (hψχ : ∀ t ∈ Icc (0 : ℝ) 1, ψ (χ t) = t) :
    windingInterval (fun t => φ (ψ t)) = windingInterval φ := by
  apply subset_antisymm
  · calc windingInterval (fun t => φ (ψ t))
        ⊆ windingInterval (fun t => φ (ψ (χ t))) :=
          windingInterval_subset_comp (φ := fun t => φ (ψ t)) hχc hχm hχ0 hχ1
      _ = windingInterval φ := windingInterval_congr fun t ht => by rw [hψχ t ht]
  · exact windingInterval_subset_comp hψc hψm hψ0 hψ1

/-! ### Time change -/

/-- The inverse of `τ(s) = ∫₀ˢ m` for a continuous, positive, `T`-periodic `m`. -/
theorem exists_time_change {m : ℝ → ℝ} (hm : Continuous m) (hpos : ∀ s, 0 < m s) {T : ℝ}
    (hT : 0 < T) (hper : ∀ s, m (s + T) = m s) :
    ∃ (τf σ : ℝ → ℝ) (QT : ℝ), 0 < QT ∧ Continuous τf ∧ Continuous σ ∧ StrictMono τf ∧
      StrictMono σ ∧ (∀ t, τf (σ t) = t) ∧ (∀ s, σ (τf s) = s) ∧ τf 0 = 0 ∧ σ 0 = 0 ∧
      τf T = QT ∧ (∀ t, σ (t + QT) = σ t + T) ∧ ∀ t, HasDerivAt σ (m (σ t))⁻¹ t := by
  set τf : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, m u with hτf
  have hd : ∀ s, HasDerivAt τf (m s) s := fun s => (hm.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hcont : Continuous τf := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  have hmono : StrictMono τf := strictMono_of_deriv_pos fun s => by rw [(hd s).deriv]; exact hpos s
  have hτ0 : τf 0 = 0 := intervalIntegral.integral_same
  -- uniform lower bound
  obtain ⟨s₀, -, hs₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le) hm.continuousOn
  have hδ : ∀ s, m s₀ ≤ m s := by
    intro s
    obtain ⟨y, hy, hys⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) hper hT s
    rw [hys]; exact hs₀ (Ico_subset_Icc_self hy)
  set δ := m s₀
  have hδpos : 0 < δ := hpos s₀
  have hg : Monotone fun s => τf s - δ * s := by
    have hgd : ∀ s, HasDerivAt (fun s => τf s - δ * s) (m s - δ) s := fun s => by
      have h := (hd s).sub ((hasDerivAt_id' s).const_mul δ)
      simp only [mul_one] at h
      exact h
    exact monotone_of_deriv_nonneg (fun s => (hgd s).differentiableAt)
      fun s => by rw [(hgd s).deriv]; linarith [hδ s]
  have hge : ∀ s, 0 ≤ s → δ * s ≤ τf s := fun s hs => by
    have := hg hs; simp only [hτ0, mul_zero, sub_zero] at this; linarith
  have hle : ∀ s, s ≤ 0 → τf s ≤ δ * s := fun s hs => by
    have := hg hs; simp only [hτ0, mul_zero, sub_zero] at this; linarith
  have htop : Tendsto τf atTop atTop :=
    tendsto_atTop_mono' atTop (eventually_ge_atTop 0 |>.mono fun s hs => hge s hs)
      (tendsto_id.const_mul_atTop hδpos)
  have hbot : Tendsto τf atBot atBot :=
    tendsto_atBot_mono' atBot (eventually_le_atBot 0 |>.mono fun s hs => hle s hs)
      (tendsto_id.const_mul_atBot hδpos)
  have hsurj := hcont.surjective htop hbot
  set e := StrictMono.orderIsoOfSurjective τf hmono hsurj
  have hτσ : ∀ t, τf (e.symm t) = t := fun t =>
    StrictMono.orderIsoOfSurjective_self_symm_apply τf hmono hsurj t
  have hστ : ∀ s, e.symm (τf s) = s := fun s =>
    StrictMono.orderIsoOfSurjective_symm_apply_self τf hmono hsurj s
  have hint : ∀ a b, IntervalIntegrable m MeasureTheory.volume a b := fun a b =>
    hm.intervalIntegrable a b
  have hadd : ∀ s, τf (s + T) = τf s + τf T := by
    intro s
    simp only [hτf]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + T))]
    congr 1
    have := Function.Periodic.intervalIntegral_add_eq (f := m) (T := T) hper s 0
    rw [this, zero_add]
  refine ⟨τf, e.symm, τf T, ?_, hcont, e.symm.continuous, hmono, e.symm.strictMono, hτσ, hστ,
    hτ0, ?_, rfl, fun t => ?_, fun t => ?_⟩
  · rw [← hτ0]; exact hmono hT
  · calc e.symm 0 = e.symm (τf 0) := by rw [hτ0]
      _ = 0 := hστ 0
  · rw [← hστ (e.symm t + T), hadd, hτσ]
  · exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hd _)
      (hpos _).ne' (Eventually.of_forall hτσ)

/-! ### Defining functions with proportional differentials -/

lemma liouvilleForm_smul_r (y v : R4) (c : ℝ) :
    liouvilleForm y (c • v) = c * liouvilleForm y v := by
  simp [liouvilleForm]; ring

lemma hvf_of_fderiv_smul {K : R4 → ℝ} {y : R4} {c : ℝ}
    (h : fderiv ℝ K y = c • fderiv ℝ H y) :
    hamiltonianVectorField K y = c • hamiltonianVectorField H y := by
  rw [hamiltonianVectorField_eq, hamiltonianVectorField_eq]; simp only; rw [h, map_smul]

lemma xiFrameRaw_of_fderiv_smul {K : R4 → ℝ} {y : R4} {c : ℝ} (hc : c ≠ 0)
    (h : fderiv ℝ K y = c • fderiv ℝ H y) (Q : R4 → R4) :
    xiFrameRaw K Q y = xiFrameRaw H Q y := by
  simp only [xiFrameRaw, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc]

lemma reebProjection_of_fderiv_smul {K : R4 → ℝ} {y : R4} {c : ℝ} (hc : c ≠ 0)
    (h : fderiv ℝ K y = c • fderiv ℝ H y) (v : R4) :
    reebProjection K y v = reebProjection H y v := by
  simp only [reebProjection, hvf_of_fderiv_smul h, liouvilleForm_smul_r, smul_smul]
  congr 2
  by_cases h0 : liouvilleForm y (hamiltonianVectorField H y) = 0
  · simp [h0]
  · field_simp

lemma reebProjection_add_hvf {y u : R4} (a : ℝ)
    (h0 : liouvilleForm y (hamiltonianVectorField H y) ≠ 0) :
    reebProjection H y (u + a • hamiltonianVectorField H y) = reebProjection H y u := by
  have hlin : liouvilleForm y (u + a • hamiltonianVectorField H y) =
      liouvilleForm y u + a * liouvilleForm y (hamiltonianVectorField H y) := by
    simp [liouvilleForm]; ring
  simp only [reebProjection, hlin]
  rw [add_div, mul_div_assoc, div_self h0, mul_one, add_smul]
  abel

/-! ### ω₀ as a continuous linear functional and the frame decomposition -/

/-- `v ↦ ω₀(u, v)`. -/
noncomputable def omegaL (u : R4) : R4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => omega0 u v
      map_add' := fun v w => by simp [omega0]; ring
      map_smul' := fun c v => by simp [omega0]; ring }

@[simp] lemma omegaL_apply (u v : R4) : omegaL u v = omega0 u v := rfl

/-- Coordinates in a frame `x, X, Z₁, Z₂` with `ω₀(x, X) = μ ≠ 0`, `ω₀(Z₁, Z₂) = 1` and
`span{Z₁, Z₂}` `ω₀`-orthogonal to `x, X`. -/
lemma frame_decomp {x X Z₁ Z₂ : R4} {μ : ℝ} (hμ : omega0 x X = μ) (hμ0 : μ ≠ 0)
    (h12 : omega0 Z₁ Z₂ = 1) (h1a : omega0 Z₁ x = 0) (h1b : omega0 Z₁ X = 0)
    (h2a : omega0 Z₂ x = 0) (h2b : omega0 Z₂ X = 0) (v : R4) :
    v = (omega0 v X / μ) • x + (omega0 x v / μ) • X + omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set a := omega0 v X / μ
  set b := omega0 x v / μ
  set v' := v - a • x - b • X with hv'
  have hva : omega0 v' x = 0 := by
    have e1 : omega0 v' x = omega0 v x - a * omega0 x x - b * omega0 X x := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, omega0_self, omega0_antisymm X x, hμ]
    simp only [b]; rw [omega0_antisymm x v]; field_simp; ring
  have hvb : omega0 v' X = 0 := by
    have e1 : omega0 v' X = omega0 v X - a * omega0 x X - b * omega0 X X := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, omega0_self, hμ]
    simp only [a]; field_simp; ring
  have hab : omega0 x X ≠ 0 := by rw [hμ]; exact hμ0
  have hf := eq_frame_of_omega0 Z₁ Z₂ x X v' h12 h1a h1b h2a h2b hab hva hvb
  have e2 : omega0 v' Z₂ = omega0 v Z₂ := by
    have e1 : omega0 v' Z₂ = omega0 v Z₂ - a * omega0 x Z₂ - b * omega0 X Z₂ := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, omega0_antisymm x, omega0_antisymm X, h2a, h2b]; ring
  have e3 : omega0 Z₁ v' = omega0 Z₁ v := by
    have e1 : omega0 Z₁ v' = omega0 Z₁ v - a * omega0 Z₁ x - b * omega0 Z₁ X := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, h1a, h1b]; ring
  rw [e2, e3] at hf
  calc v = a • x + b • X + v' := by rw [hv']; abel
    _ = _ := by rw [hf]; abel

end HryniewiczCriterion

/-!
Leaf A, part 3: orbits and linearized flows of the gauge model `K = gaugeSq H`.

On `S` we have `X_K = (2 / dH(x) x) X_H`, so `t ↦ x(σ(t))` is an orbit of `X_K` for the time
change `σ' = 2 / dH(x(σ)) x(σ)`. The linearized flow of `K` along it is built explicitly from
its columns on the frame `x₀, X_K(x₀), Z₁, Z₂`: `x(σ(t))`, `X_K(x(σ(t)))` and
`Y(σ(t)) Zⱼ + γⱼ(t) X_K(x(σ(t)))`, where `γⱼ` is an explicit integral. The `X_K`-terms are killed
by the Reeb projection, so the contact-plane paths agree up to the reparametrization `σ`.
-/


namespace HryniewiczCriterion

variable {H : R4 → ℝ}

section Transfer

variable (hS : IsStrictlyStarShapedLevel H)
include hS

lemma gaugeCoef_level_ne {y : R4} (hy : H y = 1) : (2 / fderiv ℝ H y y) ≠ 0 :=
  (div_pos two_pos (hS.2.2 y hy)).ne'

lemma hvf_gaugeSq_of_level {y : R4} (hy : H y = 1) :
    hamiltonianVectorField (gaugeSq H) y = (2 / fderiv ℝ H y y) • hamiltonianVectorField H y :=
  hvf_of_fderiv_smul (fderiv_gaugeSq_of_level hS hy)

lemma xiFrame1_gaugeSq {y : R4} (hy : H y = 1) : xiFrame1 (gaugeSq H) y = xiFrame1 H y := by
  simp only [xiFrame1,
    xiFrameRaw_of_fderiv_smul (gaugeCoef_level_ne hS hy) (fderiv_gaugeSq_of_level hS hy)]

lemma xiFrame2_gaugeSq {y : R4} (hy : H y = 1) : xiFrame2 (gaugeSq H) y = xiFrame2 H y := by
  simp only [xiFrame2,
    xiFrameRaw_of_fderiv_smul (gaugeCoef_level_ne hS hy) (fderiv_gaugeSq_of_level hS hy)]

lemma xiCoords_gaugeSq {y : R4} (hy : H y = 1) (v : R4) :
    xiCoords (gaugeSq H) y v = xiCoords H y v := by
  simp only [xiCoords, xiFrame1_gaugeSq hS hy, xiFrame2_gaugeSq hS hy]

lemma reebProjection_gaugeSq {y : R4} (hy : H y = 1) (v : R4) :
    reebProjection (gaugeSq H) y v = reebProjection H y v :=
  reebProjection_of_fderiv_smul (gaugeCoef_level_ne hS hy) (fderiv_gaugeSq_of_level hS hy) v

lemma fderiv_hvf_gaugeSq_tangent {y : R4} (hy : H y = 1) {w : R4} (hw : fderiv ℝ H y w = 0) :
    fderiv ℝ (hamiltonianVectorField (gaugeSq H)) y w =
      fderiv ℝ (gaugeCoef H) y w • hamiltonianVectorField H y +
        (2 / fderiv ℝ H y y) • fderiv ℝ (hamiltonianVectorField H) y w := by
  rw [fderiv_hvfOn hk_open (gaugeSq_contDiffOn hS) (ne_zero_of_level hS hy), fderiv_hvf hS.1,
    ContinuousLinearMap.comp_apply, fderiv2_gaugeSq_tangent hS hy hw, gaugeCoef_of_level hS hy,
    ContinuousLinearMap.comp_apply, map_add, map_smul, map_smul]
  simp only [hamiltonianVectorField_eq]

lemma gaugeCoef_fderiv_continuousOn : ContinuousOn (fderiv ℝ (gaugeCoef H)) {x | x ≠ 0} :=
  ContDiffOn.continuousOn_fderiv_of_isOpen
    (fun _ hx => (gaugeCoef_contDiffAt hS hx).contDiffWithinAt) hk_open (by simp)

/-- The linearized flow of the gauge model along the time-changed orbit `x(σ(t))`. -/
theorem gaugeSq_flow
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v)
    (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H P.x Y)
    (σ : ℝ → ℝ) (hσc : Continuous σ) (hσ0 : σ 0 = 0)
    (hσd : ∀ t, HasDerivAt σ (fderiv ℝ H (P.x (σ t)) (P.x (σ t)) / 2)⁻¹ t)
    (hQd : ∀ t, HasDerivAt (fun t => P.x (σ t))
      (hamiltonianVectorField (gaugeSq H) (P.x (σ t))) t) :
    ∃ Z : ℝ → (R4 →L[ℝ] R4), IsLinearizedFlow (gaugeSq H) (fun t => P.x (σ t)) Z ∧
      ∀ s (j : Fin 2),
        reebProjection H (P.x (σ s)) (Z s (![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] j)) =
          reebProjection H (P.x (σ s)) (Y (σ s) (![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] j)) := by
  have hK := gaugeSq_model hS hpos
  set K := gaugeSq H with hKdef
  have hPx : ∀ t, H (P.x t) = 1 := P.trajectory.2
  have hPc : Continuous P.x :=
    continuous_iff_continuousAt.2 fun t => (P.trajectory.1 t).continuousAt
  have hne : ∀ t, P.x (σ t) ≠ 0 := fun t => ne_zero_of_level hS (hPx _)
  set mP : ℝ → ℝ := fun s => fderiv ℝ H (P.x s) (P.x s) with hmP
  have hmPc : Continuous mP :=
    ((contDiff_fderiv_of_smooth hS.1).continuous.comp hPc).clm_apply hPc
  have hmPpos : ∀ s, 0 < mP s := fun s => hS.2.2 _ (hPx s)
  set x₀ := P.x 0 with hx₀
  have hm₀ : 0 < fderiv ℝ H x₀ x₀ := hS.2.2 _ (hPx 0)
  set X₀ := hamiltonianVectorField K x₀ with hX₀
  set Z₁ := xiFrame1 H x₀ with hZ₁
  set Z₂ := xiFrame2 H x₀ with hZ₂
  have hX₀' : X₀ = (2 / fderiv ℝ H x₀ x₀) • hamiltonianVectorField H x₀ :=
    hvf_gaugeSq_of_level hS (hPx 0)
  have hμ : omega0 x₀ X₀ = 2 := by
    rw [hX₀, omega0_y_X, fderiv_gaugeSq_of_level hS (hPx 0)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← hx₀]
    field_simp
  have h12 : omega0 Z₁ Z₂ = 1 := omega0_xiFrame12 hm₀
  have h1a : omega0 Z₁ x₀ = 0 := omega0_xiFrame_y quatQ2 omega0_quatQ2
  have h2a : omega0 Z₂ x₀ = 0 := omega0_xiFrame_y quatQ1 omega0_quatQ1
  have h1b : omega0 Z₁ X₀ = 0 := by
    have := omega0_xiFrame_X hm₀ quatQ2
    rw [hX₀', hZ₁, xiFrame1]
    simp only [omega0, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination (2 / fderiv ℝ H x₀ x₀) * this
  have h2b : omega0 Z₂ X₀ = 0 := by
    have := omega0_xiFrame_X hm₀ quatQ1
    rw [hX₀', hZ₂, xiFrame2]
    simp only [omega0, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination (2 / fderiv ℝ H x₀ x₀) * this
  have ht1 : fderiv ℝ H x₀ Z₁ = 0 := by
    rw [hZ₁, xiFrame1, map_smul, dH_xiFrameRaw hm₀, smul_zero]
  have ht2 : fderiv ℝ H x₀ Z₂ = 0 := by
    rw [hZ₂, xiFrame2, map_smul, dH_xiFrameRaw hm₀, smul_zero]
  -- the linearization along the orbit
  set A : ℝ → (R4 →L[ℝ] R4) := fun t => fderiv ℝ (hamiltonianVectorField K) (P.x (σ t)) with hA
  set XQ : ℝ → R4 := fun t => hamiltonianVectorField K (P.x (σ t)) with hXQ
  have hXQd : ∀ t, HasDerivAt XQ (A t (XQ t)) t := by
    intro t
    have h := (hasFDerivAt_hvfOn hk_open hK.1 (hne t)).comp_hasDerivAt t (hQd t)
    rw [← fderiv_hvfOn hk_open hK.1 (hne t)] at h
    exact h
  have hw0d : ∀ t, HasDerivAt (fun t => P.x (σ t)) (A t (P.x (σ t))) t := by
    intro t
    have h := hQd t
    rw [← hk_euler_hvf hK (hne t)] at h
    exact h
  -- the columns over the contact plane
  set g : R4 → ℝ → ℝ := fun v s =>
    fderiv ℝ (gaugeCoef H) (P.x (σ s)) (Y (σ s) v) * (mP (σ s) / 2) with hg
  set W : R4 → ℝ → R4 := fun v t =>
    Y (σ t) v + (∫ s in (0 : ℝ)..t, g v s) • XQ t with hW
  have hYc : Continuous Y :=
    continuous_iff_continuousAt.2 fun t => (hY.2 t).continuousAt
  have hgc : ∀ v, Continuous (g v) := by
    intro v
    have h1 : Continuous fun s => fderiv ℝ (gaugeCoef H) (P.x (σ s)) :=
      (gaugeCoef_fderiv_continuousOn hS).comp_continuous (hPc.comp hσc) fun s => hne s
    have h2 : Continuous fun s => Y (σ s) v :=
      (hYc.comp hσc).clm_apply continuous_const
    exact (h1.clm_apply h2).mul ((hmPc.comp hσc).div_const 2)
  have hWd : ∀ v, fderiv ℝ H x₀ v = 0 → ∀ t, HasDerivAt (W v) (A t (W v t)) t := by
    intro v hv t
    have hYσ := (hY.2 (σ t)).scomp t (hσd t)
    have hu : HasDerivAt (fun t => Y (σ t) v)
        ((fderiv ℝ H (P.x (σ t)) (P.x (σ t)) / 2)⁻¹ •
          fderiv ℝ (hamiltonianVectorField H) (P.x (σ t)) (Y (σ t) v)) t := by
      have h := hYσ.clm_apply (hasDerivAt_const t v)
      simp only [Function.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, map_zero, add_zero] at h
      exact h
    have hγ := ((hgc v).integral_hasStrictDerivAt 0 t).hasDerivAt
    have hd := hu.add (hγ.smul (hXQd t))
    refine hd.congr_deriv ?_
    have htan : fderiv ℝ H (P.x (σ t)) (Y (σ t) v) = 0 := by
      rw [dH_linearizedFlow hS.1 P.trajectory hY v (σ t)]; exact hv
    have hAu := fderiv_hvf_gaugeSq_tangent hS (hPx (σ t)) htan
    have hXQt : XQ t = (2 / fderiv ℝ H (P.x (σ t)) (P.x (σ t))) •
        hamiltonianVectorField H (P.x (σ t)) := hvf_gaugeSq_of_level hS (hPx _)
    have hm := hmPpos (σ t)
    simp only [hmP] at hm
    simp only [hW, hg, map_add, map_smul]
    rw [show A t (Y (σ t) v) = _ from hAu]
    rw [hXQt]
    simp only [map_smul, smul_smul, smul_add]
    match_scalars <;> (try simp only [hmP]) <;> field_simp
  have hW0 : ∀ v, W v 0 = v := by
    intro v
    simp only [hW, hσ0, hY.1, intervalIntegral.integral_same, zero_smul, add_zero]
    rfl
  -- assemble `Z` from its columns on the frame `x₀, X₀, Z₁, Z₂`
  set ℓ₀ : R4 →L[ℝ] ℝ := -((1 / 2 : ℝ) • omegaL X₀) with hℓ₀
  set ℓ₁ : R4 →L[ℝ] ℝ := (1 / 2 : ℝ) • omegaL x₀ with hℓ₁
  set ℓ₂ : R4 →L[ℝ] ℝ := -omegaL Z₂ with hℓ₂
  set ℓ₃ : R4 →L[ℝ] ℝ := omegaL Z₁ with hℓ₃
  have hdec : ∀ v, v = ℓ₀ v • x₀ + ℓ₁ v • X₀ + ℓ₂ v • Z₁ + ℓ₃ v • Z₂ := by
    intro v
    have h := frame_decomp hμ two_ne_zero h12 h1a h1b h2a h2b v
    have e0 : ℓ₀ v = omega0 v X₀ / 2 := by
      simp only [hℓ₀, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        omegaL_apply, smul_eq_mul]
      rw [omega0_antisymm X₀ v]; ring
    have e1 : ℓ₁ v = omega0 x₀ v / 2 := by
      simp only [hℓ₁, ContinuousLinearMap.smul_apply, omegaL_apply, smul_eq_mul]; ring
    have e2 : ℓ₂ v = omega0 v Z₂ := by
      simp only [hℓ₂, ContinuousLinearMap.neg_apply, omegaL_apply]
      rw [omega0_antisymm Z₂ v]; ring
    have e3 : ℓ₃ v = omega0 Z₁ v := rfl
    rw [e0, e1, e2, e3]; exact h
  set Z : ℝ → (R4 →L[ℝ] R4) := fun t =>
    ℓ₀.smulRight (P.x (σ t)) + ℓ₁.smulRight (XQ t) + ℓ₂.smulRight (W Z₁ t) +
      ℓ₃.smulRight (W Z₂ t) with hZ
  have hsr : ∀ (ℓ : R4 →L[ℝ] ℝ) (f : ℝ → R4) (f' : R4) (t : ℝ), HasDerivAt f f' t →
      HasDerivAt (fun t => ℓ.smulRight (f t)) (ℓ.smulRight f') t := by
    intro ℓ f f' t hf
    have h := (ContinuousLinearMap.smulRightL ℝ R4 R4 ℓ).hasFDerivAt.comp_hasDerivAt t hf
    exact h
  have hZflow : IsLinearizedFlow K (fun t => P.x (σ t)) Z := by
    refine ⟨?_, fun t => ?_⟩
    · ext1 v
      have e1 : P.x (σ 0) = x₀ := by rw [hσ0]
      have e2 : XQ 0 = X₀ := by simp only [hXQ, hσ0, hX₀, hx₀]
      simp only [hZ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, e1, e2,
        hW0, ContinuousLinearMap.id_apply]
      exact (hdec v).symm
    · have hd := (((hsr ℓ₀ _ _ t (hw0d t)).add (hsr ℓ₁ _ _ t (hXQd t))).add
        (hsr ℓ₂ _ _ t (hWd Z₁ ht1 t))).add (hsr ℓ₃ _ _ t (hWd Z₂ ht2 t))
      refine hd.congr_deriv ?_
      ext1 v
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, hZ, hA, map_add, map_smul]
  refine ⟨Z, hZflow, fun s j => ?_⟩
  have hl1 : ℓ₀ Z₁ = 0 ∧ ℓ₁ Z₁ = 0 ∧ ℓ₂ Z₁ = 1 ∧ ℓ₃ Z₁ = 0 := by
    simp only [hℓ₀, hℓ₁, hℓ₂, hℓ₃, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      omegaL_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, omega0_self _⟩
    · rw [omega0_antisymm X₀, h1b]; ring
    · rw [omega0_antisymm, h1a]; ring
    · rw [omega0_antisymm, h12]; norm_num
  have hl2 : ℓ₀ Z₂ = 0 ∧ ℓ₁ Z₂ = 0 ∧ ℓ₂ Z₂ = 0 ∧ ℓ₃ Z₂ = 1 := by
    simp only [hℓ₀, hℓ₁, hℓ₂, hℓ₃, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      omegaL_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, h12⟩
    · rw [omega0_antisymm X₀, h2b]; ring
    · rw [omega0_antisymm, h2a]; ring
    · rw [omega0_self]; ring
  have hy := hPx (σ s)
  have hlv : liouvilleForm (P.x (σ s)) (hamiltonianVectorField H (P.x (σ s))) ≠ 0 := by
    rw [liouville_X]; exact (div_pos (hS.2.2 _ hy) two_pos).ne'
  have hreeb : ∀ v, reebProjection H (P.x (σ s)) (W v s) =
      reebProjection H (P.x (σ s)) (Y (σ s) v) := by
    intro v
    simp only [hW, hXQ]
    rw [hvf_gaugeSq_of_level hS hy, smul_smul]
    exact reebProjection_add_hvf _ hlv
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    simp only [hZ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, hl1.1,
      hl1.2.1, hl1.2.2.1, hl1.2.2.2, zero_smul, one_smul, zero_add, add_zero]
    exact hreeb Z₁
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp only [hZ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, hl2.1,
      hl2.2.1, hl2.2.2.1, hl2.2.2.2, zero_smul, one_smul, zero_add, add_zero]
    exact hreeb Z₂

end Transfer

end HryniewiczCriterion

/-!
Leaf A: `exists_homogeneous_convex_model` (HWZ (3.31)–(3.32)).
-/


namespace HryniewiczCriterion

/-- A1 + A2 as a standalone statement: the gauge model and its differential on `S`. -/
theorem exists_gauge_model' (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v) :
    ∃ K : R4 → ℝ, IsHomogeneousConvexModel K ∧ energySurface K = energySurface H ∧
      ∀ y : R4, H y = 1 → fderiv ℝ K y = (2 / fderiv ℝ H y y) • fderiv ℝ H y :=
  ⟨gaugeSq H, gaugeSq_model hS hpos, gaugeSq_energySurface hS,
    fun _ hy => fderiv_gaugeSq_of_level hS hy⟩

theorem exists_homogeneous_convex_model' (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v) :
    ∃ K : R4 → ℝ, IsHomogeneousConvexModel K ∧ energySurface K = energySurface H ∧
      ∀ (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow H P.x Y →
        ∃ (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)), IsLinearizedFlow K Q.x Z ∧
          windingInterval (linearizedXiPath K Q Z) = windingInterval (linearizedXiPath H P Y) := by
  refine ⟨gaugeSq H, gaugeSq_model hS hpos, gaugeSq_energySurface hS, fun P Y hY => ?_⟩
  have hPx : ∀ t, H (P.x t) = 1 := P.trajectory.2
  have hPc : Continuous P.x :=
    continuous_iff_continuousAt.2 fun t => (P.trajectory.1 t).continuousAt
  set mP : ℝ → ℝ := fun s => fderiv ℝ H (P.x s) (P.x s) with hmP
  have hmPc : Continuous mP :=
    ((contDiff_fderiv_of_smooth hS.1).continuous.comp hPc).clm_apply hPc
  have hmPpos : ∀ s, 0 < mP s := fun s => hS.2.2 _ (hPx s)
  obtain ⟨τf, σ, QT, hQT, hτc, hσc, hτm, hσm, hτσ, hστ, hτ0, hσ0, hτT, hσper, hσd⟩ :=
    exists_time_change (m := fun s => mP s / 2) (hmPc.div_const 2)
      (fun s => div_pos (hmPpos s) two_pos) P.T_pos (fun s => by simp only [hmP, P.periodic])
  have hσd' : ∀ t, HasDerivAt σ (fderiv ℝ H (P.x (σ t)) (P.x (σ t)) / 2)⁻¹ t := hσd
  have hQd : ∀ t, HasDerivAt (fun t => P.x (σ t))
      (hamiltonianVectorField (gaugeSq H) (P.x (σ t))) t := by
    intro t
    have h := (P.trajectory.1 (σ t)).scomp t (hσd' t)
    rw [hvf_gaugeSq_of_level hS (hPx _), ← inv_div]
    exact h
  let Q : PeriodicOrbit (gaugeSq H) :=
    { x := fun t => P.x (σ t)
      T := QT
      T_pos := hQT
      trajectory := ⟨hQd, fun t => (gaugeSq_eq_one_iff hS _).2 (hPx _)⟩
      periodic := fun t => by
        show P.x (σ (t + QT)) = P.x (σ t)
        rw [hσper, P.periodic] }
  obtain ⟨Z, hZ, hcol⟩ := gaugeSq_flow hS hpos P Y hY σ hσc hσ0 hσd' hQd
  refine ⟨Q, Z, hZ, ?_⟩
  have hPT := P.T_pos
  have hσQT : σ QT = P.T := by
    have := hσper 0; rwa [zero_add, hσ0, zero_add] at this
  have hpath : linearizedXiPath (gaugeSq H) Q Z =
      fun τ => linearizedXiPath H P Y (σ (QT * τ) / P.T) := by
    funext τ
    ext i j
    have hT : P.T * (σ (QT * τ) / P.T) = σ (QT * τ) := by field_simp
    have hy := hPx (σ (QT * τ))
    have h0 := hPx 0
    show xiCoords (gaugeSq H) (P.x (σ (QT * τ))) (reebProjection (gaugeSq H) (P.x (σ (QT * τ)))
        (Z (QT * τ) (![xiFrame1 (gaugeSq H) (P.x (σ 0)), xiFrame2 (gaugeSq H) (P.x (σ 0))] j))) i
      = _
    rw [hσ0, xiFrame1_gaugeSq hS h0, xiFrame2_gaugeSq hS h0, xiCoords_gaugeSq hS hy,
      reebProjection_gaugeSq hS hy, hcol]
    simp only [linearizedXiPath, Matrix.of_apply, hT]
  rw [hpath]
  have hσmono := hσm.monotone
  have hτmono := hτm.monotone
  refine windingInterval_comp_reparam (ψ := fun τ => σ (QT * τ) / P.T)
    (χ := fun u => τf (P.T * u) / QT) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ((hσc.comp (continuous_const.mul continuous_id)).div_const _).continuousOn
  · rintro τ ⟨h0, h1⟩
    constructor
    · apply div_nonneg _ hPT.le
      rw [← hσ0]; exact hσmono (mul_nonneg hQT.le h0)
    · rw [div_le_one hPT, ← hσQT]; exact hσmono (by nlinarith)
  · simp only [mul_zero, hσ0, zero_div]
  · simp only [mul_one, hσQT, div_self hPT.ne']
  · exact ((hτc.comp (continuous_const.mul continuous_id)).div_const _).continuousOn
  · rintro u ⟨h0, h1⟩
    constructor
    · apply div_nonneg _ hQT.le
      rw [← hτ0]; exact hτmono (mul_nonneg hPT.le h0)
    · rw [div_le_one hQT, ← hτT]; exact hτmono (by nlinarith)
  · simp only [mul_zero, hτ0, zero_div]
  · simp only [mul_one, hτT, div_self hQT.ne']
  · intro u _
    have e : QT * (τf (P.T * u) / QT) = τf (P.T * u) := by field_simp
    show σ (QT * (τf (P.T * u) / QT)) / P.T = u
    rw [e, hστ]; field_simp

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (hpos : ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ H) x v v) :
    ∃ K : R4 → ℝ, IsHomogeneousConvexModel K ∧ energySurface K = energySurface H ∧
      ∀ y : R4, H y = 1 → fderiv ℝ K y = (2 / fderiv ℝ H y y) • fderiv ℝ H y :=
  exists_gauge_model' H hS hpos
