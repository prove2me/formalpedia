-- Prove2me | solution 1 for HryniewiczCriterion.det_graphUnitary4_eq_div_star
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:05:40.096953+00:00
-- url     : https://prove2.me/submissions/7b8b3bee-875a-448f-a512-9a516ee78d3d

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
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

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

/-!
# Complex-linear parts of real `4 × 4` matrices (leaf D, algebra)

For a real `4 × 4` matrix `g` acting on `ℂ² ≅ ℝ⁴` (`zₖ = q_k + i p_k`), write `g z = A z + C z̄`.
`A = cA g` is the complex-linear part, `cCb g = C̄`. Then `cA (g h) = cA g cA h + cC g cCb h`,
`det graphBasis4 g = 4 det (cA g)` and `det graphUnitary4 g = d / d̄` with `d = det (cA g)`.
For symplectic `g₁, g₂` the ratio `d(g₁ g₂) / (d(g₁) d(g₂)) = det (1 + X Y)` with contractions
`X, Y`, hence lies in the slit plane.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

/-- The complex-linear part of a real `4 × 4` matrix, as a complex `2 × 2` matrix. -/
def cA (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(g 0 0 + g 1 1) / 2, (g 1 0 - g 0 1) / 2⟩, ⟨(g 0 2 + g 1 3) / 2, (g 1 2 - g 0 3) / 2⟩;
     ⟨(g 2 0 + g 3 1) / 2, (g 3 0 - g 2 1) / 2⟩, ⟨(g 2 2 + g 3 3) / 2, (g 3 2 - g 2 3) / 2⟩]

/-- The anti-linear part `C` (`g z = A z + C z̄`). -/
def cC (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(g 0 0 - g 1 1) / 2, (g 1 0 + g 0 1) / 2⟩, ⟨(g 0 2 - g 1 3) / 2, (g 1 2 + g 0 3) / 2⟩;
     ⟨(g 2 0 - g 3 1) / 2, (g 3 0 + g 2 1) / 2⟩, ⟨(g 2 2 - g 3 3) / 2, (g 3 2 + g 2 3) / 2⟩]

/-- The complex conjugate `C̄` of the anti-linear part. -/
def cCb (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟨(g 0 0 - g 1 1) / 2, -((g 1 0 + g 0 1) / 2)⟩, ⟨(g 0 2 - g 1 3) / 2, -((g 1 2 + g 0 3) / 2)⟩;
     ⟨(g 2 0 - g 3 1) / 2, -((g 3 0 + g 2 1) / 2)⟩, ⟨(g 2 2 - g 3 3) / 2, -((g 3 2 + g 2 3) / 2)⟩]

/-- `d(g) = det_ℂ (cA g)`. -/
def cdet (g : Matrix (Fin 4) (Fin 4) ℝ) : ℂ := (cA g).det

lemma cA_mul (g h : Matrix (Fin 4) (Fin 4) ℝ) : cA (g * h) = cA g * cA h + cC g * cCb h := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cA, cC, cCb, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, Complex.ext_iff] <;>
    constructor <;> ring

lemma cA_one : cA 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cA, Complex.ext_iff, Matrix.one_apply]

lemma cC_one : cC 1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cC, Complex.ext_iff, Matrix.one_apply]

lemma cdet_one : cdet 1 = 1 := by simp [cdet, cA_one]

lemma graphBasis4_eq (g : Matrix (Fin 4) (Fin 4) ℝ) : graphBasis4 g =
    !![1, -I, 0, 0; 0, 0, 1, -I;
      (g 0 0 : ℂ) + I * g 1 0, (g 0 1 : ℂ) + I * g 1 1, (g 0 2 : ℂ) + I * g 1 2, (g 0 3 : ℂ) + I * g 1 3;
      (g 2 0 : ℂ) + I * g 3 0, (g 2 1 : ℂ) + I * g 3 1, (g 2 2 : ℂ) + I * g 3 2, (g 2 3 : ℂ) + I * g 3 3] := by
  ext r k; fin_cases r <;> fin_cases k <;> simp [graphBasis4, Matrix.one_apply]

lemma det_graphBasis4 (g : Matrix (Fin 4) (Fin 4) ℝ) : (graphBasis4 g).det = 4 * cdet g := by
  rw [graphBasis4_eq, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three]
  simp [Matrix.submatrix_apply, Fin.succAbove, Fin.lt_def, cdet, cA, Matrix.det_fin_two]
  apply Complex.ext <;> simp <;> ring

end

end HryniewiczCriterion

/-!
# Leaf D, algebra II: `det graphUnitary4 = d / d̄` and the slit-plane factorization

For `g₁ Ω g₁ᵀ = Ω` and `g₂ᵀ Ω g₂ = Ω`, `d(g₁ g₂) / (d(g₁) d(g₂)) = det (1 + X Y)` with
`X = A₁⁻¹ C₁` a weak and `Y = C̄₂ A₂⁻¹` a strict contraction, so it lies in the slit plane.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

lemma det_lagUnitary {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.det ≠ 0) :
    (lagUnitary A).det = A.det / star A.det := by
  have hs : star A.det ≠ 0 := star_ne_zero.mpr hA
  unfold lagUnitary
  rw [det_mul, det_mul, det_nonsing_inv, det_mul, det_conjTranspose, det_transpose,
    Ring.inverse_eq_inv']
  field_simp

lemma det_graphUnitary4 {g : Matrix (Fin 4) (Fin 4) ℝ} (h : cdet g ≠ 0) :
    (graphUnitary4 g).det = cdet g / star (cdet g) := by
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  have hg : (graphBasis4 g).det ≠ 0 := by rw [det_graphBasis4]; exact mul_ne_zero h4 h
  have h1 : (graphBasis4 1).det ≠ 0 := by rw [det_graphBasis4, cdet_one]; norm_num
  have hs : star (cdet g) ≠ 0 := star_ne_zero.mpr h
  unfold graphUnitary4
  rw [det_mul, det_nonsing_inv, det_lagUnitary hg, det_lagUnitary h1, det_graphBasis4,
    det_graphBasis4, cdet_one, Ring.inverse_eq_inv']
  simp only [star_mul', mul_one]
  have : star (4 : ℂ) = 4 := by simp
  rw [this]
  field_simp

/-! ### Symplectic matrices -/

lemma omegaMat_mul_self : omegaMat * omegaMat = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_four]

lemma sp_mul_transpose {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g * omegaMat * g.transpose = omegaMat := by
  have h1 : (-(omegaMat * g.transpose * omegaMat)) * g = 1 := by
    have : (-(omegaMat * g.transpose * omegaMat)) * g =
        -(omegaMat * (g.transpose * omegaMat * g)) := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, h, omegaMat_mul_self, neg_neg]
  have h2 := mul_eq_one_comm.1 h1
  have : (g * (-(omegaMat * g.transpose * omegaMat))) * omegaMat = g * omegaMat * g.transpose := by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, omegaMat_mul_self, Matrix.mul_one,
      neg_neg]
  rw [← this, h2, Matrix.one_mul]

lemma sp_transpose_of {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g * omegaMat * g.transpose = omegaMat) :
    g.transpose * omegaMat * g = omegaMat := by
  have := sp_mul_transpose (g := g.transpose) (by rwa [Matrix.transpose_transpose])
  rwa [Matrix.transpose_transpose] at this

lemma sp_mul {g h : Matrix (Fin 4) (Fin 4) ℝ} (hg : g.transpose * omegaMat * g = omegaMat)
    (hh : h.transpose * omegaMat * h = omegaMat) :
    (g * h).transpose * omegaMat * (g * h) = omegaMat := by
  rw [Matrix.transpose_mul]
  calc h.transpose * g.transpose * omegaMat * (g * h)
      = h.transpose * (g.transpose * omegaMat * g) * h := by simp only [Matrix.mul_assoc]
    _ = omegaMat := by rw [hg, hh]

lemma sp_id1 {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    (cA g)ᴴ * cA g = 1 + (cCb g)ᴴ * cCb g := by
  have e : ∀ a b, omega0 (fun k => g k a) (fun k => g k b) = omegaMat a b := fun a b => by
    rw [← transpose_omega_mul_apply, h]
  have h01 := e 0 1; have h02 := e 0 2; have h03 := e 0 3
  have h12 := e 1 2; have h13 := e 1 3; have h23 := e 2 3
  simp only [omega0] at h01 h02 h03 h12 h13 h23
  simp [omegaMat] at h01 h02 h03 h12 h13 h23
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cA, cCb, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff, Matrix.one_apply] <;>
    (try constructor) <;>
    first
      | ring1
      | linear_combination h01 | linear_combination -h01
      | linear_combination h23 | linear_combination -h23
      | linear_combination (1/2) * h03 - (1/2) * h12 | linear_combination -(1/2) * h03 + (1/2) * h12
      | linear_combination (1/2) * h02 + (1/2) * h13 | linear_combination -(1/2) * h02 - (1/2) * h13

lemma sp_id2 {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g * omegaMat * g.transpose = omegaMat) :
    cA g * (cA g)ᴴ = 1 + cC g * (cC g)ᴴ := by
  have e : ∀ a b, omega0 (fun k => g a k) (fun k => g b k) = omegaMat a b := fun a b => by
    have := transpose_omega_mul_apply g.transpose a b
    rw [Matrix.transpose_transpose, h] at this
    rw [this]; rfl
  have h01 := e 0 1; have h02 := e 0 2; have h03 := e 0 3
  have h12 := e 1 2; have h13 := e 1 3; have h23 := e 2 3
  simp only [omega0] at h01 h02 h03 h12 h13 h23
  simp [omegaMat] at h01 h02 h03 h12 h13 h23
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [cA, cC, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Complex.ext_iff, Matrix.one_apply] <;>
    (try constructor) <;>
    first
      | ring1
      | linear_combination h01 | linear_combination -h01
      | linear_combination h23 | linear_combination -h23
      | linear_combination (1/2) * h03 - (1/2) * h12 | linear_combination -(1/2) * h03 + (1/2) * h12
      | linear_combination (1/2) * h02 + (1/2) * h13 | linear_combination -(1/2) * h02 - (1/2) * h13

/-! ### Contractions on `ℂ²` -/

/-- The squared Hermitian norm on `ℂ²`. -/
def nsq (v : Fin 2 → ℂ) : ℝ := normSq (v 0) + normSq (v 1)

lemma nsq_nonneg (v : Fin 2 → ℂ) : 0 ≤ nsq v := add_nonneg (normSq_nonneg _) (normSq_nonneg _)

lemma nsq_pos {v : Fin 2 → ℂ} (hv : v ≠ 0) : 0 < nsq v := by
  rcases (nsq_nonneg v).lt_or_eq with h | h
  · exact h
  · exfalso; apply hv
    have h0 : normSq (v 0) = 0 := by
      have := normSq_nonneg (v 0); have := normSq_nonneg (v 1); unfold nsq at h; linarith
    have h1 : normSq (v 1) = 0 := by
      have := normSq_nonneg (v 0); have := normSq_nonneg (v 1); unfold nsq at h; linarith
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1

lemma star_dotProduct_self (v : Fin 2 → ℂ) : star v ⬝ᵥ v = (nsq v : ℂ) := by
  simp [dotProduct, Fin.sum_univ_two, nsq, normSq_eq_conj_mul_self]

lemma star_mulVec_dotProduct (M N : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (N *ᵥ v) = star v ⬝ᵥ ((Mᴴ * N) *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]

lemma nsq_mulVec_of {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ * M = 1 + Nᴴ * N) (v : Fin 2 → ℂ) :
    nsq (M *ᵥ v) = nsq v + nsq (N *ᵥ v) := by
  have e := star_mulVec_dotProduct M M v
  rw [h, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← star_mulVec_dotProduct N N v,
    star_dotProduct_self, star_dotProduct_self, star_dotProduct_self] at e
  exact_mod_cast e

lemma det_ne_zero_of_id {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ * M = 1 + Nᴴ * N) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have e := nsq_mulVec_of h v
  rw [hMv] at e
  have h0 : nsq (0 : Fin 2 → ℂ) = 0 := by simp [nsq]
  have := nsq_pos hv; have := nsq_nonneg (N *ᵥ v); linarith

lemma nsq_bound_eq {M N : Matrix (Fin 2) (Fin 2) ℂ} (h : Mᴴ * M = 1 + Nᴴ * N) (v : Fin 2 → ℂ) :
    nsq ((N * M⁻¹) *ᵥ v) + nsq (M⁻¹ *ᵥ v) = nsq v := by
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_id h)
  have hz : M *ᵥ (M⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have e := nsq_mulVec_of h (M⁻¹ *ᵥ v)
  rw [hz] at e
  rw [← mulVec_mulVec]
  linarith

lemma normSq_dotProduct_le (a b : Fin 2 → ℂ) : normSq (star a ⬝ᵥ b) ≤ nsq a * nsq b := by
  have key : nsq a * nsq b - normSq (star a ⬝ᵥ b) = normSq (a 0 * b 1 - a 1 * b 0) := by
    simp [nsq, dotProduct, Fin.sum_univ_two, normSq_apply]; ring
  have := normSq_nonneg (a 0 * b 1 - a 1 * b 0); linarith

/-- `X = A⁻¹ C` is a weak contraction when `A Aᴴ = 1 + C Cᴴ`. -/
lemma weak_contraction {A C : Matrix (Fin 2) (Fin 2) ℂ} (h : A * Aᴴ = 1 + C * Cᴴ)
    (v : Fin 2 → ℂ) : nsq ((A⁻¹ * C) *ᵥ v) ≤ nsq v := by
  have h' : (Aᴴ)ᴴ * Aᴴ = 1 + (Cᴴ)ᴴ * Cᴴ := by simpa using h
  set X := A⁻¹ * C
  have hXH : Xᴴ = Cᴴ * (Aᴴ)⁻¹ := by
    simp only [X, conjTranspose_mul, conjTranspose_nonsing_inv]
  have hstar : ∀ u, nsq (Xᴴ *ᵥ u) ≤ nsq u := fun u => by
    have := nsq_bound_eq h' u; rw [hXH]; have := nsq_nonneg ((Aᴴ)⁻¹ *ᵥ u); linarith
  clear_value X
  have e := star_mulVec_dotProduct X X v
  rw [star_dotProduct_self, ← mulVec_mulVec] at e
  have hcs := normSq_dotProduct_le v (Xᴴ *ᵥ (X *ᵥ v))
  rw [← e, normSq_ofReal] at hcs
  have h2 := hstar (X *ᵥ v)
  have hp := nsq_nonneg (X *ᵥ v)
  have hv := nsq_nonneg v
  by_contra hlt
  push_neg at hlt
  nlinarith [mul_le_mul_of_nonneg_left h2 hv]

/-- `Y = C̄ A⁻¹` is a strict contraction when `Aᴴ A = 1 + C̄ᴴ C̄`. -/
lemma strict_contraction {A Cb : Matrix (Fin 2) (Fin 2) ℂ} (h : Aᴴ * A = 1 + Cbᴴ * Cb)
    {v : Fin 2 → ℂ} (hv : v ≠ 0) : nsq ((Cb * A⁻¹) *ᵥ v) < nsq v := by
  have e := nsq_bound_eq h v
  have hz : A⁻¹ *ᵥ v ≠ 0 := by
    intro h0
    have hu : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_id h)
    apply hv
    rw [← one_mulVec v, ← mul_nonsing_inv _ hu, ← mulVec_mulVec, h0, mulVec_zero]
  have := nsq_pos hz
  linarith

lemma mul_mem_slitPlane_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    a * b ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : (a * b).im = 0
  · left
    simp only [mul_im] at him
    simp only [mul_re]
    have h1 : a.re * (a.re * b.re - a.im * b.im) = (a.re ^ 2 + a.im ^ 2) * b.re := by
      linear_combination (-a.im) * him
    have h2 : 0 < (a.re ^ 2 + a.im ^ 2) * b.re := by positivity
    by_contra hle; push_neg at hle
    nlinarith
  · exact Or.inr him

/-- If `X` is a weak and `Y` a strict contraction of `ℂ²`, `det (1 + X Y)` avoids `(-∞, 0]`. -/
lemma det_one_add_mul_mem_slitPlane {X Y : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : ∀ v, nsq (X *ᵥ v) ≤ nsq v) (hY : ∀ v, v ≠ 0 → nsq (Y *ᵥ v) < nsq v) :
    (1 + X * Y).det ∈ slitPlane := by
  set Z := X * Y
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (Z.trace ^ 2 - 4 * Z.det)
  have hev : ∀ μ : ℂ, μ ^ 2 - Z.trace * μ + Z.det = 0 → 0 < (1 + μ).re := by
    intro μ hμ
    have hd : (Z - μ • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
      rw [det_fin_two]; rw [trace_fin_two, det_fin_two] at hμ
      simp [Matrix.one_apply]; linear_combination hμ
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hZv : Z *ᵥ v = μ • v := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hv; exact hv
    have h1 : nsq (Z *ᵥ v) = normSq μ * nsq v := by
      rw [hZv]; simp [nsq, normSq_mul]; ring
    have h2 : nsq (Z *ᵥ v) < nsq v := by
      simp only [Z]; rw [← mulVec_mulVec]; exact (hX _).trans_lt (hY v hv0)
    have hpos := nsq_pos hv0
    have hμ1 : normSq μ < 1 := by
      by_contra hc; push_neg at hc; nlinarith
    have : μ.re ^ 2 ≤ normSq μ := by rw [normSq_apply]; nlinarith [sq_nonneg μ.im]
    simp only [add_re, one_re]
    nlinarith
  set μ₁ := (Z.trace + s) / 2
  set μ₂ := (Z.trace - s) / 2
  have e1 : μ₁ ^ 2 - Z.trace * μ₁ + Z.det = 0 := by simp only [μ₁]; linear_combination (-1/4) * hs
  have e2 : μ₂ ^ 2 - Z.trace * μ₂ + Z.det = 0 := by simp only [μ₂]; linear_combination (-1/4) * hs
  have hdet : (1 + Z).det = (1 + μ₁) * (1 + μ₂) := by
    have : (1 + Z).det = 1 + Z.trace + Z.det := by
      rw [det_fin_two, det_fin_two, trace_fin_two]; simp [Matrix.one_apply]; ring
    rw [this]; simp only [μ₁, μ₂]; linear_combination (-1/4) * hs
  rw [hdet]
  exact mul_mem_slitPlane_of_re_pos (hev _ e1) (hev _ e2)

lemma cdet_ne_zero {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    cdet g ≠ 0 := det_ne_zero_of_id (sp_id1 h)

/-- The slit-plane factorization: for `g₁ Ω g₁ᵀ = Ω` and `g₂ᵀ Ω g₂ = Ω`,
`d(g₁ g₂) / (d(g₁) d(g₂)) = det (1 + X Y)` lies in the slit plane. -/
lemma cdet_mul_ratio_mem_slitPlane {g₁ g₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h₁ : g₁ * omegaMat * g₁.transpose = omegaMat) (h₂ : g₂.transpose * omegaMat * g₂ = omegaMat) :
    cdet (g₁ * g₂) / (cdet g₁ * cdet g₂) ∈ slitPlane := by
  have i1 := sp_id2 h₁
  have i2 := sp_id1 h₂
  have hA1 : (cA g₁).det ≠ 0 := by
    have : ((cA g₁)ᴴ)ᴴ * (cA g₁)ᴴ = 1 + ((cC g₁)ᴴ)ᴴ * (cC g₁)ᴴ := by simpa using i1
    have := det_ne_zero_of_id this
    rwa [det_conjTranspose, star_ne_zero] at this
  have hA2 : (cA g₂).det ≠ 0 := det_ne_zero_of_id i2
  have u1 : IsUnit (cA g₁).det := isUnit_iff_ne_zero.2 hA1
  have u2 : IsUnit (cA g₂).det := isUnit_iff_ne_zero.2 hA2
  set X := (cA g₁)⁻¹ * cC g₁
  set Y := cCb g₂ * (cA g₂)⁻¹
  have hfac : cA (g₁ * g₂) = cA g₁ * (1 + X * Y) * cA g₂ := by
    rw [cA_mul]
    simp only [X, Y, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [nonsing_inv_mul _ u2, Matrix.mul_one, ← Matrix.mul_assoc (cA g₁), mul_nonsing_inv _ u1,
      Matrix.one_mul]
  have hr : cdet (g₁ * g₂) / (cdet g₁ * cdet g₂) = (1 + X * Y).det := by
    unfold cdet; rw [hfac, det_mul, det_mul]; field_simp
  rw [hr]
  exact det_one_add_mul_mem_slitPlane (weak_contraction i1) (fun v hv => strict_contraction i2 hv)

end

end HryniewiczCriterion

/-!
# Leaf D, pointwise facts: frame determinant, `blockOne`, polar decomposition

* `i · d(F(y))` has positive real part for the frame `F(y) = homogFrame H y` whenever
  `dH(y) y > 0`: `Re (i d(F)) = |y|⁻¹ (2|y|² + 2⟨y, w⟩ + |D|²) / 4` with `w = ∇H / dH(y)y`.
* `F(y)` is symplectic.
* `d(blockOne m) = c(m) = ((m₀₀ + m₁₁) + i (m₁₀ - m₀₁)) / 2`, and `m = R(α) P` with `P ≻ 0` when
  `c(m) = r e^{iα}`, `r > 0`, `det m = 1`.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

variable {H : R4 → ℝ}

/-- The frame with columns `y`, `J w`, `m (Q₂y - ⟨w, Q₂y⟩ y)`, `m (Q₁y - ⟨w, Q₁y⟩ y)`. -/
def frameW (y w : R4) (m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => (![y, ![-w 1, w 0, -w 3, w 2],
    m • (quatQ2 y - dot4 w (quatQ2 y) • y), m • (quatQ1 y - dot4 w (quatQ1 y) • y)] j) i

lemma re_I_cdet_frameW (y w : R4) (m : ℝ) :
    (I * cdet (frameW y w m)).re = m * (2 * dot4 y y + 2 * dot4 y w +
      (w 0 * y 2 - w 1 * y 3 - w 2 * y 0 + w 3 * y 1) ^ 2 +
      (w 0 * y 3 + w 1 * y 2 - w 2 * y 1 - w 3 * y 0) ^ 2) / 4 := by
  simp [cdet, cA, frameW, det_fin_two, dot4, Fin.sum_univ_four, quatQ1, quatQ2, Matrix.vecHead,
    Matrix.vecTail, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

lemma homogFrame_eq_frameW {y : R4} (hy : 0 < fderiv ℝ H y y) :
    homogFrame H y = frameW y (fun i => partialDeriv H y i / fderiv ℝ H y y) (euclidNorm y)⁻¹ := by
  have hs := hy.ne'
  have hL : ∀ v, fderiv ℝ H y v / fderiv ℝ H y y =
      dot4 (fun i => partialDeriv H y i / fderiv ℝ H y y) v := by
    intro v; rw [clm_apply_eq_sum (fderiv ℝ H y) v]
    simp only [dot4, Fin.sum_univ_four, partialDeriv]; field_simp
  have hω : omega0 y (hamiltonianVectorField H y) = fderiv ℝ H y y := omega0_y_X y
  ext i j
  fin_cases j
  · rfl
  · simp only [homogFrame, frameW, Matrix.of_apply, hω]
    fin_cases i <;> simp [hamiltonianVectorField] <;> (try field_simp)
  · simp only [homogFrame, frameW, Matrix.of_apply, xiFrame1, xiFrameRaw, hL]
    rfl
  · simp only [homogFrame, frameW, Matrix.of_apply, xiFrame2, xiFrameRaw, hL]
    rfl

lemma re_I_cdet_homogFrame_pos {y : R4} (hy : 0 < fderiv ℝ H y y) :
    0 < (I * cdet (homogFrame H y)).re := by
  have hy0 : y ≠ 0 := ne_zero_of_dH_pos hy
  rw [homogFrame_eq_frameW hy, re_I_cdet_frameW]
  set w : R4 := fun i => partialDeriv H y i / fderiv ℝ H y y
  have hyw : dot4 y w = 1 := by
    have h1 : dot4 y w * fderiv ℝ H y y = fderiv ℝ H y y := by
      conv_rhs => rw [clm_apply_eq_sum (fderiv ℝ H y) y]
      simp only [w, dot4, Fin.sum_univ_four, partialDeriv]; field_simp
    have h2 := hy.ne'
    calc dot4 y w = dot4 y w * fderiv ℝ H y y / fderiv ℝ H y y := by field_simp
      _ = 1 := by rw [h1, div_self h2]
  have hm : 0 < (euclidNorm y)⁻¹ := by
    have : 0 < euclidNorm y := Real.sqrt_pos.2 (dot4_pos hy0)
    positivity
  have hd := dot4_pos hy0
  rw [hyw]
  positivity

lemma homogFrame_sp {y : R4} (hy : 0 < fderiv ℝ H y y) :
    (homogFrame H y).transpose * omegaMat * homogFrame H y = omegaMat := by
  set X0 := hamiltonianVectorField H y
  set c := (omega0 y X0)⁻¹
  have hωxX : omega0 y X0 = fderiv ℝ H y y := omega0_y_X y
  set Z1 := xiFrame1 H y
  set Z2 := xiFrame2 H y
  have h12 : omega0 Z1 Z2 = 1 := omega0_xiFrame12 hy
  have h1x : omega0 Z1 y = 0 := omega0_xiFrame_y quatQ2 omega0_quatQ2
  have h2x : omega0 Z2 y = 0 := omega0_xiFrame_y quatQ1 omega0_quatQ1
  have h1X : omega0 Z1 X0 = 0 := omega0_xiFrame_X hy quatQ2
  have h2X : omega0 Z2 X0 = 0 := omega0_xiFrame_X hy quatQ1
  have hxX0 : omega0 y X0 ≠ 0 := by rw [hωxX]; exact hy.ne'
  have hcol : ∀ j, (fun k => homogFrame H y k j) = ![y, c • X0, Z1, Z2] j := fun j => rfl
  have hsr : ∀ (u v : R4) (a : ℝ), omega0 u (a • v) = a * omega0 u v := by
    intros; simp [omega0]; ring
  have p01 : omega0 y (c • X0) = 1 := by rw [hsr]; exact inv_mul_cancel₀ hxX0
  have p10 : omega0 (c • X0) y = -1 := by rw [omega0_antisymm, p01]
  have p21 : omega0 Z1 (c • X0) = 0 := by rw [hsr, h1X, mul_zero]
  have p31 : omega0 Z2 (c • X0) = 0 := by rw [hsr, h2X, mul_zero]
  have p12 : omega0 (c • X0) Z1 = 0 := by rw [omega0_antisymm, p21, neg_zero]
  have p13 : omega0 (c • X0) Z2 = 0 := by rw [omega0_antisymm, p31, neg_zero]
  have p02 : omega0 y Z1 = 0 := by rw [omega0_antisymm, h1x, neg_zero]
  have p03 : omega0 y Z2 = 0 := by rw [omega0_antisymm, h2x, neg_zero]
  have p32 : omega0 Z2 Z1 = -1 := by rw [omega0_antisymm, h12]
  ext i j
  rw [transpose_omega_mul_apply, hcol, hcol]
  fin_cases i <;> fin_cases j <;>
    simp [omegaMat, omega0_self, p01, p10, p21, p31, p12, p13, p02, p03, p32, h12, h1x, h2x]

/-! ### `blockOne` -/

/-- `c(m) = ((m₀₀ + m₁₁) + i (m₁₀ - m₀₁)) / 2`, the complex-linear part of a real `2 × 2` matrix. -/
def polarC (m : Matrix (Fin 2) (Fin 2) ℝ) : ℂ := ⟨(m 0 0 + m 1 1) / 2, (m 1 0 - m 0 1) / 2⟩

lemma cdet_blockOne (m : Matrix (Fin 2) (Fin 2) ℝ) : cdet (blockOne m) = polarC m := by
  simp [cdet, cA, blockOne, det_fin_two, polarC, Complex.ext_iff]

lemma blockOne_one : blockOne 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [blockOne, Matrix.one_apply]

lemma blockOne_sp {m : Matrix (Fin 2) (Fin 2) ℝ} (h : m.det = 1) :
    (blockOne m).transpose * omegaMat * blockOne m = omegaMat := by
  rw [det_fin_two] at h
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [blockOne, omegaMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
      | ring1 | linear_combination h | linear_combination -h | linear_combination 2 * h
      | linear_combination -2 * h

lemma one_le_normSq_polarC {m : Matrix (Fin 2) (Fin 2) ℝ} (h : m.det = 1) :
    1 ≤ normSq (polarC m) := by
  rw [det_fin_two] at h
  simp only [polarC, normSq_mk]
  nlinarith [sq_nonneg (m 0 0 - m 1 1), sq_nonneg (m 0 1 + m 1 0)]

lemma polarC_ne_zero {m : Matrix (Fin 2) (Fin 2) ℝ} (h : m.det = 1) : polarC m ≠ 0 := by
  intro h0; have := one_le_normSq_polarC h; rw [h0, map_zero] at this; norm_num at this

lemma rotationMatrix_mul_neg (a : ℝ) : rotationMatrix a * rotationMatrix (-a) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;>
    nlinarith [Real.sin_sq_add_cos_sq a]

/-- Polar decomposition from the angle of `c(m)`. -/
lemma polar_of_polarC {m : Matrix (Fin 2) (Fin 2) ℝ} (hdet : m.det = 1) {α r : ℝ} (hr : 0 < r)
    (hc : polarC m = r * exp (α * I)) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧ m = rotationMatrix α * P := by
  refine ⟨rotationMatrix (-α) * m, ?_, ?_⟩
  · have hre : (m 0 0 + m 1 1) / 2 = r * Real.cos α := by
      have := congrArg Complex.re hc
      simpa [polarC, exp_mul_I, ← ofReal_cos, ← ofReal_sin, mul_re] using this
    have him : (m 1 0 - m 0 1) / 2 = r * Real.sin α := by
      have := congrArg Complex.im hc
      simpa [polarC, exp_mul_I, ← ofReal_cos, ← ofReal_sin, mul_im] using this
    rw [det_fin_two] at hdet
    set c := Real.cos α
    set s := Real.sin α
    have hcs : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    set P := rotationMatrix (-α) * m with hP
    have e00 : P 0 0 = c * m 0 0 + s * m 1 0 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have e01 : P 0 1 = c * m 0 1 + s * m 1 1 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have e10 : P 1 0 = -s * m 0 0 + c * m 1 0 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have e11 : P 1 1 = -s * m 0 1 + c * m 1 1 := by
      simp [hP, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg, c, s,
        Matrix.vecMul, dotProduct]
    have hsym : P 1 0 = P 0 1 := by
      rw [e10, e01]; linear_combination (2 * c) * him - (2 * s) * hre
    have htr : P 0 0 + P 1 1 = 2 * r := by
      rw [e00, e11]; linear_combination (2 * c) * hre + (2 * s) * him + 2 * r * hcs
    have hdP : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 1 := by
      rw [e00, e01, e10, e11]; linear_combination hdet + (m 0 0 * m 1 1 - m 0 1 * m 1 0 - 1) * 0 +
        (m 0 0 * m 1 1 - m 0 1 * m 1 0) * hcs
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [hsym]
    · have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra hc; push_neg at hc; apply hv; ext i; fin_cases i <;> simp [hc.1, hc.2]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, star_trivial]
      rw [hsym]
      rw [hsym] at hdP
      have ha : 0 < P 0 0 := by
        by_contra hc; push_neg at hc
        nlinarith [sq_nonneg (P 0 1), mul_nonneg (neg_nonneg.2 hc) (sq_nonneg (P 0 1))]
      have hq : P 0 0 * (v 0 * (P 0 0 * v 0 + P 0 1 * v 1) + v 1 * (P 0 1 * v 0 + P 1 1 * v 1)) =
          (P 0 0 * v 0 + P 0 1 * v 1) ^ 2 + (P 0 0 * P 1 1 - P 0 1 * P 0 1) * v 1 ^ 2 := by ring
      have hpos : 0 < (P 0 0 * v 0 + P 0 1 * v 1) ^ 2 + (P 0 0 * P 1 1 - P 0 1 * P 0 1) * v 1 ^ 2 := by
        rcases hv' with h0 | h1
        · by_cases h1 : v 1 = 0
          · rw [h1]
            have hne : P 0 0 * v 0 ≠ 0 := mul_ne_zero ha.ne' h0
            have := pow_pos (abs_pos.2 hne) 2; rw [sq_abs] at this; nlinarith
          · have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this
            nlinarith [sq_nonneg (P 0 0 * v 0 + P 0 1 * v 1)]
        · have := pow_pos (abs_pos.2 h1) 2; rw [sq_abs] at this
          nlinarith [sq_nonneg (P 0 0 * v 0 + P 0 1 * v 1)]
      have := hq ▸ hpos
      exact pos_of_mul_pos_right this ha.le
  · rw [← Matrix.mul_assoc, rotationMatrix_mul_neg, Matrix.one_mul]

end

end HryniewiczCriterion

/-!
# Leaf D, analytic helpers

* `z / z̄ = e^{2 i arg z}`;
* continuity of `cdet` and of `arg` on the slit plane;
* a continuous polar angle of a path in `SL(2, ℝ)` (path lifting through `exp : ℂ → ℂ \ {0}`);
* the frame-flow factorization `Y(t) F(x₀) = F(x(t)) blockOne(φ(t / T))` for every `t`.
-/

namespace HryniewiczCriterion

open Matrix Complex
open scoped ContDiff

noncomputable section

/-! ### `z / z̄` -/

lemma ofReal_mul_exp_div_star (r : ℝ) (hr : r ≠ 0) (a : ℝ) :
    (r * exp (a * I)) / star (r * exp (a * I)) = exp ((2 * a : ℝ) * I) := by
  have hs : star (r * exp (a * I)) = r * exp (-(a * I)) := by
    rw [star_mul', Complex.star_def, conj_ofReal, ← exp_conj, map_mul,
      conj_ofReal, conj_I, mul_neg]
  rw [hs, mul_div_mul_left _ _ (ofReal_ne_zero.2 hr), ← exp_sub]
  congr 1; push_cast; ring

lemma div_star_eq_exp_arg {z : ℂ} (hz : z ≠ 0) :
    z / star z = exp ((2 * arg z : ℝ) * I) := by
  have h := norm_mul_exp_arg_mul_I z
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  conv_lhs => rw [← h]
  exact ofReal_mul_exp_div_star _ hn _

lemma div_star_mul (a b : ℂ) : (a * b) / star (a * b) = (a / star a) * (b / star b) := by
  rw [star_mul', mul_div_mul_comm]

lemma div_star_div (a b : ℂ) : (a / b) / star (a / b) = (a / star a) / (b / star b) := by
  rw [star_div₀, div_div_div_comm]

/-! ### Continuity -/

lemma continuousOn_complex_mk {s : Set ℝ} {a b : ℝ → ℝ} (ha : ContinuousOn a s)
    (hb : ContinuousOn b s) : ContinuousOn (fun t => (⟨a t, b t⟩ : ℂ)) s := by
  have e : (fun t => (⟨a t, b t⟩ : ℂ)) = fun t => (a t : ℂ) + (b t : ℂ) * I :=
    funext fun t => by apply Complex.ext <;> simp
  rw [e]
  exact (continuous_ofReal.comp_continuousOn ha).add
    ((continuous_ofReal.comp_continuousOn hb).mul continuousOn_const)

lemma continuousOn_cdet {s : Set ℝ} {g : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hg : ∀ i j, ContinuousOn (fun t => g t i j) s) : ContinuousOn (fun t => cdet (g t)) s := by
  have hA : ∀ k l, ContinuousOn (fun t => cA (g t) k l) s := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp only [cA] <;> simp <;>
      exact continuousOn_complex_mk
        ((((hg _ _).add (hg _ _)).div_const 2)) (((hg _ _).sub (hg _ _)).div_const 2)
  simp only [cdet, det_fin_two]
  exact ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))

lemma continuousOn_mul_entries {s : Set ℝ} {g h : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hg : ∀ i j, ContinuousOn (fun t => g t i j) s) (hh : ∀ i j, ContinuousOn (fun t => h t i j) s)
    (i j : Fin 4) : ContinuousOn (fun t => (g t * h t) i j) s := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  exact ((((hg i 0).mul (hh 0 j)).add ((hg i 1).mul (hh 1 j))).add ((hg i 2).mul (hh 2 j))).add
    ((hg i 3).mul (hh 3 j))

lemma continuousOn_arg_comp {s : Set ℝ} {f : ℝ → ℂ} (hf : ContinuousOn f s)
    (hs : ∀ t ∈ s, f t ∈ slitPlane) : ContinuousOn (fun t => arg (f t)) s :=
  fun t ht => (continuousAt_arg (hs t ht)).comp_continuousWithinAt (hf t ht)

/-! ### The polar angle of a path in `SL(2, ℝ)` -/

/-- A continuous angle `α` with `c(φ(τ)) = r e^{iα(τ)}`, `r > 0`, `α(0) = 0`, for a continuous
path `φ` in `SL(2, ℝ)` on `[0, 1]` starting at `1`. -/
lemma exists_polarC_lift {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ i j, ContinuousOn (fun τ => φ τ i j) (Set.Icc 0 1))
    (hdet : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (φ τ).det = 1) (h0 : φ 0 = 1) :
    ∃ α : ℝ → ℝ, Continuous α ∧ α 0 = 0 ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧ polarC (φ τ) = r * exp (α τ * I) := by
  have hpc : ContinuousOn (fun τ => polarC (φ τ)) (Set.Icc 0 1) :=
    continuousOn_complex_mk (((hc 0 0).add (hc 1 1)).div_const 2)
      (((hc 1 0).sub (hc 0 1)).div_const 2)
  let γ : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun τ => ⟨polarC (φ τ), polarC_ne_zero (hdet τ τ.2)⟩,
      (hpc.restrict).subtype_mk _⟩
  have γ0 : γ 0 = (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) 0 := by
    apply Subtype.ext
    show polarC (φ 0) = exp 0
    rw [h0, exp_zero]
    simp [polarC, Complex.ext_iff]
  obtain ⟨Γ, hΓ, hΓ0⟩ := isCoveringMap_exp.exists_path_lifts γ 0 γ0
  refine ⟨fun τ => (Γ (Set.projIcc 0 1 zero_le_one τ)).im,
    (continuous_im.comp Γ.continuous).comp continuous_projIcc, ?_, ?_⟩
  · simp only
    rw [Set.projIcc_left]
    have : (⟨0, Set.left_mem_Icc.2 zero_le_one⟩ : Set.Icc (0 : ℝ) 1) = (0 : unitInterval) := rfl
    rw [this, hΓ0, zero_im]
  · intro τ hτ
    have hp := congrFun hΓ ⟨τ, hτ⟩
    have he : exp (Γ ⟨τ, hτ⟩) = polarC (φ τ) := congrArg Subtype.val hp
    refine ⟨Real.exp (Γ ⟨τ, hτ⟩).re, Real.exp_pos _, ?_⟩
    simp only
    rw [Set.projIcc_of_mem _ hτ, ← he]
    conv_lhs => rw [← re_add_im (Γ ⟨τ, hτ⟩)]
    rw [exp_add, ofReal_exp]

/-! ### The frame-flow factorization at every time -/

theorem frame_flow_factor (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) (t : ℝ) :
    LinearMap.toMatrix' (Z t : R4 →ₗ[ℝ] R4) * homogFrame K (Q.x 0) =
      homogFrame K (Q.x t) * blockOne (linearizedXiPath K Q Z (t / Q.T)) := by
  set U : Set R4 := {x | x ≠ 0} with hUdef
  have hU : IsOpen U := hk_open
  have hH : ContDiffOn ℝ ∞ K U := hK.1
  have hK1 : ∀ t, K (Q.x t) = 1 := Q.trajectory.2
  have hxU : ∀ t, Q.x t ∈ U := fun t h => by
    have := hK1 t; rw [h, hk_zero hK] at this; norm_num at this
  have hpos : ∀ t, 0 < fderiv ℝ K (Q.x t) (Q.x t) := fun t => by
    rw [hk_euler hK (hxU t), hK1]; norm_num
  have hxsol : ∀ t, Q.x t = Z t (Q.x 0) := by
    refine flow_solution_eq hU hH hxU hZ (fun t => ?_)
    have h := Q.trajectory.1 t
    rw [← hk_euler_hvf hK (hxU t), fderiv_hvfOn hU hH (hxU t)] at h
    exact h
  have hXsol : ∀ t, hamiltonianVectorField K (Q.x t) = Z t (hamiltonianVectorField K (Q.x 0)) :=
    flow_solution_eq hU hH hxU hZ (w := fun t => hamiltonianVectorField K (Q.x t))
      (fun s => (hasFDerivAt_hvfOn hU hH (hxU s)).comp_hasDerivAt s (Q.trajectory.1 s))
  have hω : ∀ s, omega0 (Q.x s) (hamiltonianVectorField K (Q.x s)) = 2 := fun s => by
    rw [omega0_y_X, hk_euler hK (hxU s), hK1]; norm_num
  set x0 := Q.x 0
  set y := Q.x t
  set X0 := hamiltonianVectorField K x0
  set Xt := hamiltonianVectorField K y
  have hTt : Q.T * (t / Q.T) = t := mul_div_cancel₀ t Q.T_pos.ne'
  set φt := linearizedXiPath K Q Z (t / Q.T)
  have hx0 := hpos 0
  have hy := hpos t
  set Z1 := xiFrame1 K x0
  set Z2 := xiFrame2 K x0
  have h1x : omega0 Z1 x0 = 0 := omega0_xiFrame_y quatQ2 omega0_quatQ2
  have h2x : omega0 Z2 x0 = 0 := omega0_xiFrame_y quatQ1 omega0_quatQ1
  have h1X : omega0 Z1 X0 = 0 := omega0_xiFrame_X hx0 quatQ2
  have h2X : omega0 Z2 X0 = 0 := omega0_xiFrame_X hx0 quatQ1
  set W1 := xiFrame1 K y
  set W2 := xiFrame2 K y
  have g12 : omega0 W1 W2 = 1 := omega0_xiFrame12 hy
  have g1x : omega0 W1 y = 0 := omega0_xiFrame_y quatQ2 omega0_quatQ2
  have g2x : omega0 W2 y = 0 := omega0_xiFrame_y quatQ1 omega0_quatQ1
  have g1X : omega0 W1 Xt = 0 := omega0_xiFrame_X hy quatQ2
  have g2X : omega0 W2 Xt = 0 := omega0_xiFrame_X hy quatQ1
  have hyX : omega0 y Xt ≠ 0 := by rw [hω t]; norm_num
  have hZx : Z t x0 = y := (hxsol t).symm
  have hZX : Z t X0 = Xt := (hXsol t).symm
  have hcolT : ∀ j : Fin 2, Z t (![Z1, Z2] j) = φt 0 j • W1 + φt 1 j • W2 := by
    intro j
    set v := Z t (![Z1, Z2] j)
    have hvx : omega0 v y = 0 := by
      rw [← hZx, omega0_linearizedFlowOn hU hH hxU hZ]
      fin_cases j <;> simp [h1x, h2x]
    have hvX : omega0 v Xt = 0 := by
      rw [← hZX, omega0_linearizedFlowOn hU hH hxU hZ]
      fin_cases j <;> simp [h1X, h2X]
    have hreeb : reebProjection K y v = v := by
      have : liouvilleForm y v = 0 := by
        rw [liouvilleForm_eq, omega0_antisymm, hvx]; simp
      simp [reebProjection, this]
    have hφ : ∀ i, φt i j = xiCoords K y v i := by
      intro i
      rw [← hreeb]
      simp only [φt, linearizedXiPath, Matrix.of_apply]
      rw [hTt]
    rw [hφ, hφ]
    exact eq_frame_of_omega0 W1 W2 y Xt v g12 g1x g1X g2x g2X hyX hvx hvX
  have hc : (omega0 x0 X0)⁻¹ = (omega0 y Xt)⁻¹ := by rw [hω 0, hω t]
  have hFent : ∀ i m, homogFrame K x0 i m = ![x0, (omega0 x0 X0)⁻¹ • X0, Z1, Z2] m i :=
    fun _ _ => rfl
  have hGent : ∀ i m, homogFrame K y i m = ![y, (omega0 y Xt)⁻¹ • Xt, W1, W2] m i :=
    fun _ _ => rfl
  have hc0 := hcolT 0
  have hc1 := hcolT 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc0 hc1
  ext i j
  rw [mul_apply_eq_apply_col, Matrix.mul_apply]
  have hcol : (fun k => homogFrame K x0 k j) = ![x0, (omega0 x0 X0)⁻¹ • X0, Z1, Z2] j := rfl
  rw [hcol]
  fin_cases j <;>
    simp [hZx, hZX, hc0, hc1, blockOne, Fin.sum_univ_four, hGent, map_smul, hc] <;> ring

end

end HryniewiczCriterion

/-!
# Leaf D: `homogeneous_graph_angle_transport`

With `G = F(x₀)⁻¹`, `F_t = F(x(t))`, `B_t = blockOne(φ(t/T))` and `Ŷ(t) = G F_t B_t`:
`d(Ŷ(t)) · w₁(0) ν(0) = w₂(t) w₁(t) ν(t) c(φ(t/T))`, where `ν = i d(F_t)` has positive real part
and `w₁ = d(G F_t)/(d(G) d(F_t))`, `w₂ = d(G F_t B_t)/(d(G F_t) d(B_t))` lie in the slit plane.
So `θ = 2 (arg w₂ + arg w₁ + arg ν + α(t/T) - arg w₁(0) - arg ν(0))` is a continuous determinant
angle, and `θ(T) = 2 α(1)` because `x(T) = x(0)` and `G F_T = 1`.
-/

namespace HryniewiczCriterion

open Matrix Complex
open scoped ContDiff

noncomputable section

lemma sp_inv_mul_self {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g⁻¹ * g = 1 := by
  have h1 : (-(omegaMat * g.transpose * omegaMat)) * g = 1 := by
    have : (-(omegaMat * g.transpose * omegaMat)) * g =
        -(omegaMat * (g.transpose * omegaMat * g)) := by
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, h, omegaMat_mul_self, neg_neg]
  rw [Matrix.inv_eq_left_inv h1, h1]

lemma sp_inv {g : Matrix (Fin 4) (Fin 4) ℝ} (h : g.transpose * omegaMat * g = omegaMat) :
    g⁻¹ * omegaMat * g⁻¹.transpose = omegaMat := by
  have hgi := sp_inv_mul_self h
  calc g⁻¹ * omegaMat * g⁻¹.transpose
      = g⁻¹ * (g * omegaMat * g.transpose) * g⁻¹.transpose := by rw [sp_mul_transpose h]
    _ = (g⁻¹ * g) * omegaMat * (g⁻¹ * g).transpose := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = omegaMat := by rw [hgi]; simp

theorem homogeneous_graph_angle_transport' (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) :
    ∃ θ α : ℝ → ℝ, IsDetAngleLift (fun t => graphUnitary4 (frameFlowMatrix K Q Z t)) Q.T θ ∧
      IsPolarAngleLift (linearizedXiPath K Q Z) α ∧ θ Q.T = 2 * α 1 := by
  set U : Set R4 := {x | x ≠ 0} with hUdef
  have hU : IsOpen U := hk_open
  have hH : ContDiffOn ℝ ∞ K U := hK.1
  have hK1 : ∀ t, K (Q.x t) = 1 := Q.trajectory.2
  have hxU : ∀ t, Q.x t ∈ U := fun t h => by
    have := hK1 t; rw [h, hk_zero hK] at this; norm_num at this
  have hpos : ∀ t, 0 < fderiv ℝ K (Q.x t) (Q.x t) := fun t => by
    rw [hk_euler hK (hxU t), hK1]; norm_num
  obtain ⟨⟨hφcd, hφdet, hφ0⟩, -, -, -⟩ := homogeneous_frame_flow_split' K hK Q Z hZ
  have hTpos := Q.T_pos
  set T := Q.T with hT
  set φ := linearizedXiPath K Q Z with hφ
  have hφc : ∀ i j, ContinuousOn (fun τ => φ τ i j) (Set.Icc 0 1) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn
      hφcd.continuousOn)
  set F : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t => homogFrame K (Q.x t) with hFdef
  set G := (F 0)⁻¹ with hGdef
  set B : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t => blockOne (φ (t / T)) with hBdef
  -- symplectic facts
  have hFsp : ∀ t, (F t).transpose * omegaMat * F t = omegaMat := fun t => homogFrame_sp (hpos t)
  have hGF0 : G * F 0 = 1 := sp_inv_mul_self (hFsp 0)
  have hG1 : G * omegaMat * G.transpose = omegaMat := sp_inv (hFsp 0)
  have hG2 : G.transpose * omegaMat * G = omegaMat := sp_transpose_of hG1
  have hGFsp : ∀ t, (G * F t).transpose * omegaMat * (G * F t) = omegaMat := fun t =>
    sp_mul hG2 (hFsp t)
  have hmem : ∀ t ∈ Set.Icc 0 T, t / T ∈ Set.Icc (0 : ℝ) 1 := fun t ht =>
    ⟨div_nonneg ht.1 hTpos.le, (div_le_one hTpos).2 ht.2⟩
  have hBsp : ∀ t ∈ Set.Icc 0 T, (B t).transpose * omegaMat * B t = omegaMat := fun t ht =>
    blockOne_sp (hφdet _ (hmem t ht))
  have hD0 : ∀ t, frameFlowMatrix K Q Z t = G * F t * B t := fun t => by
    simp only [frameFlowMatrix, Matrix.mul_assoc]
    rw [frame_flow_factor K hK Q Z hZ t]
  -- nonvanishing
  have hdG : cdet G ≠ 0 := cdet_ne_zero hG2
  have hdF : ∀ t, cdet (F t) ≠ 0 := fun t => cdet_ne_zero (hFsp t)
  have hdGF : ∀ t, cdet (G * F t) ≠ 0 := fun t => cdet_ne_zero (hGFsp t)
  have hdB : ∀ t ∈ Set.Icc 0 T, cdet (B t) ≠ 0 := fun t ht => by
    simp only [hBdef]; rw [cdet_blockOne]; exact polarC_ne_zero (hφdet _ (hmem t ht))
  have hdY : ∀ t ∈ Set.Icc 0 T, cdet (G * F t * B t) ≠ 0 := fun t ht =>
    cdet_ne_zero (sp_mul (hGFsp t) (hBsp t ht))
  -- the three factors
  set ν : ℝ → ℂ := fun t => I * cdet (F t) with hν
  set w1 : ℝ → ℂ := fun t => cdet (G * F t) / (cdet G * cdet (F t)) with hw1
  set w2 : ℝ → ℂ := fun t => cdet (G * F t * B t) / (cdet (G * F t) * cdet (B t)) with hw2
  have hνs : ∀ t, ν t ∈ slitPlane := fun t =>
    mem_slitPlane_iff.2 (Or.inl (re_I_cdet_homogFrame_pos (hpos t)))
  have hw1s : ∀ t, w1 t ∈ slitPlane := fun t => cdet_mul_ratio_mem_slitPlane hG1 (hFsp t)
  have hw2s : ∀ t ∈ Set.Icc 0 T, w2 t ∈ slitPlane := fun t ht =>
    cdet_mul_ratio_mem_slitPlane (sp_mul_transpose (hGFsp t)) (hBsp t ht)
  have hne : ∀ z : ℂ, z ∈ slitPlane → z ≠ 0 := fun z hz => slitPlane_ne_zero hz
  -- continuity
  have hx : ContDiff ℝ ∞ Q.x := trajectory_contDiffOn hU hH Q.trajectory hxU
  have hXc : ContDiff ℝ ∞ (fun t => hamiltonianVectorField K (Q.x t)) :=
    (cdOn_hvf hU hH).comp_contDiff hx hxU
  have hFc : ∀ i j, Continuous fun t => F t i j := by
    intro i j
    have hω : Continuous fun t => omega0 (Q.x t) (hamiltonianVectorField K (Q.x t)) :=
      (cd_omega0 hx hXc).continuous
    have hωne : ∀ t, omega0 (Q.x t) (hamiltonianVectorField K (Q.x t)) ≠ 0 := fun t => by
      rw [omega0_y_X]; exact (hpos t).ne'
    have h1 := (cd_xiFrameOn hU hH hx hxU hpos quatQ2 (cd_quatQ2 hx)).continuous
    have h2 := (cd_xiFrameOn hU hH hx hxU hpos quatQ1 (cd_quatQ1 hx)).continuous
    fin_cases j
    · exact (continuous_apply i).comp hx.continuous
    · show Continuous fun t => ((omega0 (Q.x t) (hamiltonianVectorField K (Q.x t)))⁻¹ •
        hamiltonianVectorField K (Q.x t)) i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact (hω.inv₀ hωne).mul ((continuous_apply i).comp hXc.continuous)
    · exact (continuous_apply i).comp h1
    · exact (continuous_apply i).comp h2
  have hFcO : ∀ i j, ContinuousOn (fun t => F t i j) (Set.Icc 0 T) := fun i j =>
    (hFc i j).continuousOn
  have hGcO : ∀ i j, ContinuousOn (fun _ : ℝ => G i j) (Set.Icc 0 T) := fun _ _ =>
    continuousOn_const
  have hdiv : ContinuousOn (fun t : ℝ => t / T) (Set.Icc 0 T) :=
    continuousOn_id.div_const T
  have hBcO : ∀ i j, ContinuousOn (fun t => B t i j) (Set.Icc 0 T) := by
    intro i j
    have hφT : ∀ k l, ContinuousOn (fun t => φ (t / T) k l) (Set.Icc 0 T) := fun k l =>
      (hφc k l).comp hdiv (fun t ht => hmem t ht)
    fin_cases i <;> fin_cases j <;> simp only [hBdef, blockOne] <;> simp <;>
      first | exact continuousOn_const | exact hφT _ _
  have hGFcO := continuousOn_mul_entries hGcO hFcO
  have hYcO := continuousOn_mul_entries hGFcO hBcO
  have hνc : ContinuousOn ν (Set.Icc 0 T) :=
    continuousOn_const.mul (continuousOn_cdet hFcO)
  have hw1c : ContinuousOn w1 (Set.Icc 0 T) :=
    (continuousOn_cdet hGFcO).div (continuousOn_const.mul (continuousOn_cdet hFcO))
      fun t _ => mul_ne_zero hdG (hdF t)
  have hw2c : ContinuousOn w2 (Set.Icc 0 T) :=
    (continuousOn_cdet hYcO).div ((continuousOn_cdet hGFcO).mul (continuousOn_cdet hBcO))
      fun t ht => mul_ne_zero (hdGF t) (hdB t ht)
  -- the polar angle
  obtain ⟨α, hαc, hα0, hαr⟩ := exists_polarC_lift hφc hφdet hφ0
  -- endpoint values
  have hB0 : B 0 = 1 := by simp only [hBdef, zero_div]; rw [hφ0, blockOne_one]
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hTpos.le⟩
  have hTmem : T ∈ Set.Icc 0 T := ⟨hTpos.le, le_rfl⟩
  have hFT : F T = F 0 := by simp only [hFdef]; rw [show Q.x T = Q.x 0 by simpa using Q.periodic 0]
  have hw2_0 : w2 0 = 1 := by
    simp only [hw2]; rw [hGF0, hB0, Matrix.mul_one, cdet_one]; simp
  have hw2_T : w2 T = 1 := by
    simp only [hw2]; rw [hFT, hGF0, Matrix.one_mul, cdet_one, one_mul]
    exact div_self (hdB T hTmem)
  refine ⟨fun t => 2 * (arg (w2 t) + arg (w1 t) + arg (ν t) + α (t / T) - arg (w1 0) -
    arg (ν 0)), α, ⟨?_, ?_, ?_⟩, ⟨hαc.continuousOn, hα0, ?_⟩, ?_⟩
  · -- continuity
    refine ContinuousOn.mul continuousOn_const ?_
    exact ((((continuousOn_arg_comp hw2c hw2s).add
      (continuousOn_arg_comp hw1c fun t _ => hw1s t)).add
      (continuousOn_arg_comp hνc fun t _ => hνs t)).add (hαc.comp_continuousOn hdiv)).sub
      continuousOn_const |>.sub continuousOn_const
  · simp only [zero_div, hα0, hw2_0, arg_one]; ring
  · intro t ht
    have hYt := hD0 t
    simp only
    rw [hYt, det_graphUnitary4 (hdY t ht)]
    obtain ⟨r, hr, hcr⟩ := hαr (t / T) (hmem t ht)
    have hcB : cdet (B t) = polarC (φ (t / T)) := cdet_blockOne _
    -- the key identity
    have key : cdet (G * F t * B t) =
        w2 t * w1 t * ν t * (r * exp (α (t / T) * I)) / (w1 0 * ν 0) := by
      rw [← hcr, ← hcB]
      simp only [hw1, hw2, hν]
      rw [hGF0, cdet_one]
      have := hdB t ht; have := hdF t; have := hdF 0; have := hdGF t
      field_simp
    have s1 := hne _ (hw2s t ht); have s2 := hne _ (hw1s t); have s3 := hne _ (hνs t)
    have s4 := hne _ (hw1s 0); have s5 := hne _ (hνs 0)
    rw [key]
    generalize w2 t = a at s1 ⊢
    generalize w1 t = b at s2 ⊢
    generalize ν t = c at s3 ⊢
    generalize w1 0 = d at s4 ⊢
    generalize ν 0 = e at s5 ⊢
    rw [div_star_div, div_star_mul (a * b * c), div_star_mul (a * b), div_star_mul a,
      div_star_mul d,
      div_star_eq_exp_arg s1, div_star_eq_exp_arg s2,
      div_star_eq_exp_arg s3, ofReal_mul_exp_div_star r hr.ne',
      div_star_eq_exp_arg s4, div_star_eq_exp_arg s5]
    simp only [← Complex.exp_add, ← Complex.exp_sub]
    congr 1; push_cast; ring
  · intro τ hτ
    obtain ⟨r, hr, hcr⟩ := hαr τ hτ
    exact polar_of_polarC (hφdet τ hτ) hr hcr
  · simp only [div_self hTpos.ne', hw2_T, arg_one]
    have e1 : w1 T = w1 0 := by simp only [hw1]; rw [hFT]
    have e2 : ν T = ν 0 := by simp only [hν]; rw [hFT]
    rw [e1, e2]; ring

end

end HryniewiczCriterion

/-! Platform-vocabulary statements of the reusable children of leaf D. -/


namespace HryniewiczCriterion

open Matrix Complex

lemma transpose_omega_eq_of_omega0 {g : Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ u v : R4, omega0 (g *ᵥ u) (g *ᵥ v) = omega0 u v) :
    g.transpose * omegaMat * g = omegaMat := by
  ext i j
  rw [transpose_omega_mul_apply]
  have e : ∀ k, (fun l => g l k) = g *ᵥ Pi.single k 1 := fun k => by
    ext l; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, e, h]
  fin_cases i <;> fin_cases j <;> simp [omega0, omegaMat, Pi.single_apply]

lemma omega0_mulVec_of_transpose {g : Matrix (Fin 4) (Fin 4) ℝ}
    (h : g.transpose * omegaMat * g = omegaMat) (u v : R4) :
    omega0 (g *ᵥ u) (g *ᵥ v) = omega0 u v := by
  have e : ∀ w z : R4, omega0 w z = w ⬝ᵥ (omegaMat *ᵥ z) := fun w z => by
    simp [omega0, omegaMat, dotProduct, Matrix.mulVec, Fin.sum_univ_four]; ring
  rw [e, e]
  calc (g *ᵥ u) ⬝ᵥ (omegaMat *ᵥ (g *ᵥ v)) = (u ᵥ* g.transpose) ⬝ᵥ (omegaMat *ᵥ (g *ᵥ v)) := by
        rw [Matrix.vecMul_transpose]
    _ = u ⬝ᵥ (g.transpose *ᵥ (omegaMat *ᵥ (g *ᵥ v))) := by rw [Matrix.dotProduct_mulVec u g.transpose]
    _ = u ⬝ᵥ ((g.transpose * omegaMat * g) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = u ⬝ᵥ (omegaMat *ᵥ v) := by rw [h]

end HryniewiczCriterion

theorem HryniewiczCriterion.det_graphUnitary4_eq_div_star' (g : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : (graphBasis4 g).det ≠ 0) :
    (graphUnitary4 g).det = (graphBasis4 g).det / star (graphBasis4 g).det := by
  rw [det_graphBasis4] at hg ⊢
  have hd : cdet g ≠ 0 := right_ne_zero_of_mul hg
  rw [det_graphUnitary4 hd, star_mul']
  have : star (4 : ℂ) = 4 := by simp
  rw [this, mul_div_mul_left _ _ (by norm_num : (4 : ℂ) ≠ 0)]

theorem HryniewiczCriterion.graphBasis4_det_mul_ratio_mem_slitPlane'
    (g₁ g₂ : Matrix (Fin 4) (Fin 4) ℝ)
    (h₁ : ∀ u v : R4, omega0 (g₁.mulVec u) (g₁.mulVec v) = omega0 u v)
    (h₂ : ∀ u v : R4, omega0 (g₂.mulVec u) (g₂.mulVec v) = omega0 u v) :
    (graphBasis4 g₁).det ≠ 0 ∧ (graphBasis4 g₂).det ≠ 0 ∧
      4 * (graphBasis4 (g₁ * g₂)).det / ((graphBasis4 g₁).det * (graphBasis4 g₂).det) ∈
        Complex.slitPlane := by
  have s1 := transpose_omega_eq_of_omega0 h₁
  have s2 := transpose_omega_eq_of_omega0 h₂
  have d1 := cdet_ne_zero s1
  have d2 := cdet_ne_zero s2
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  refine ⟨by rw [det_graphBasis4]; exact mul_ne_zero h4 d1,
    by rw [det_graphBasis4]; exact mul_ne_zero h4 d2, ?_⟩
  have := cdet_mul_ratio_mem_slitPlane (sp_mul_transpose s1) s2
  rw [det_graphBasis4, det_graphBasis4, det_graphBasis4]
  convert this using 1
  field_simp

theorem HryniewiczCriterion.exists_polarAngleLift' (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ContinuousOn (fun t i j => φ t i j) (Set.Icc 0 1))
    (hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (h0 : φ 0 = 1) :
    ∃ α : ℝ → ℝ, IsPolarAngleLift φ α := by
  have hφc : ∀ i j, ContinuousOn (fun τ => φ τ i j) (Set.Icc 0 1) := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  obtain ⟨α, hαc, hα0, hαr⟩ := exists_polarC_lift hφc hdet h0
  refine ⟨α, hαc.continuousOn, hα0, fun τ hτ => ?_⟩
  obtain ⟨r, hr, hcr⟩ := hαr τ hτ
  exact polar_of_polarC (hdet τ hτ) hr hcr

theorem HryniewiczCriterion.frameFlowMatrix_eq_frame_mul_blockOne' (K : R4 → ℝ)
    (hK : IsHomogeneousConvexModel K) (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4))
    (hZ : IsLinearizedFlow K Q.x Z) (t : ℝ) :
    frameFlowMatrix K Q Z t = (homogFrame K (Q.x 0))⁻¹ * homogFrame K (Q.x t) *
      blockOne (linearizedXiPath K Q Z (t / Q.T)) := by
  simp only [frameFlowMatrix, Matrix.mul_assoc]
  rw [frame_flow_factor K hK Q Z hZ t]

theorem HryniewiczCriterion.homogFrame_symplectic_det_pos' (H : R4 → ℝ) (y : R4)
    (hy : 0 < fderiv ℝ H y y) :
    (∀ u v : R4, omega0 ((homogFrame H y).mulVec u) ((homogFrame H y).mulVec v) = omega0 u v) ∧
      0 < (Complex.I * (graphBasis4 (homogFrame H y)).det).re := by
  refine ⟨omega0_mulVec_of_transpose (homogFrame_sp hy), ?_⟩
  rw [det_graphBasis4, mul_left_comm]
  have e : (4 * (Complex.I * cdet (homogFrame H y))).re = 4 * (Complex.I * cdet (homogFrame H y)).re := by
    simp
  rw [e]
  exact mul_pos (by norm_num) (re_I_cdet_homogFrame_pos hy)

open HryniewiczCriterion

theorem solution (g : Matrix (Fin 4) (Fin 4) ℝ)
    (hg : (graphBasis4 g).det ≠ 0) :
    (graphUnitary4 g).det = (graphBasis4 g).det / star (graphBasis4 g).det :=
  det_graphUnitary4_eq_div_star' g hg
