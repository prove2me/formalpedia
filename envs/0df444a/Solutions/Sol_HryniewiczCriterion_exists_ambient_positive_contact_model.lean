-- Prove2me | solution 1 for HryniewiczCriterion.exists_ambient_positive_contact_model
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T23:06:08.664455+00:00
-- url     : https://prove2.me/submissions/1b6adeec-4300-4acb-8774-c71ce9f43501

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Operator.Bilinear

open scoped ContDiff Topology
open Filter

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

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-- A function with positive derivative at `r` is below `f r` just left of `r` and above
it just right of `r`. -/
lemma local_sign_of_deriv_pos {f : ℝ → ℝ} {d r : ℝ} (hf : HasDerivAt f d r) (hd : 0 < d) :
    ∃ ε > 0, (∀ t, r < t → t < r + ε → f r < f t) ∧ (∀ t, r - ε < t → t < r → f t < f r) := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hf
  have hev : ∀ᶠ y in 𝓝[≠] r, 0 < slope f r y := hs.eventually (lt_mem_nhds hd)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, h⟩ := hev
  refine ⟨ε, hε, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
  · have := h (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) (ne_of_gt h1)
    rw [slope_def_field] at this
    have hpos : 0 < t - r := by linarith
    have := (div_pos_iff.1 this).resolve_right (fun h => by linarith [h.2])
    linarith [this.1]
  · have := h (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) (ne_of_lt h2)
    rw [slope_def_field] at this
    have := (div_pos_iff.1 this).resolve_left (fun h => by linarith [h.2])
    linarith [this.1]

lemma hasDerivAt_ray (hH : ContDiff ℝ ∞ H) (u : R4) (t : ℝ) :
    HasDerivAt (fun s : ℝ => H (s • u)) (fderiv ℝ H (t • u) u) t := by
  have hd : DifferentiableAt ℝ H (t • u) := hH.differentiable (by simp) _
  have h1 : HasDerivAt (fun s : ℝ => s • u) u t := by
    simpa using (hasDerivAt_id t).smul_const u
  exact hd.hasFDerivAt.comp_hasDerivAt t h1

lemma continuous_ray (hH : ContDiff ℝ ∞ H) (u : R4) : Continuous fun s : ℝ => H (s • u) :=
  hH.continuous.comp (continuous_id.smul continuous_const)

/-- On the ray through `u`, `H` is above `1` just after the crossing radius and below `1`
just before it. -/
lemma ray_cross (hS : IsStrictlyStarShapedLevel H) {u : R4} {r : ℝ} (hr : 0 < r)
    (h1 : H (r • u) = 1) :
    ∃ ε > 0, (∀ t, r < t → t < r + ε → 1 < H (t • u)) ∧
      (∀ t, r - ε < t → t < r → H (t • u) < 1) := by
  have hd := hasDerivAt_ray hS.1 u r
  have hpos : 0 < fderiv ℝ H (r • u) u := by
    have := hS.2.2 _ h1
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr.le
  obtain ⟨ε, hε, ha, hb⟩ := local_sign_of_deriv_pos hd hpos
  refine ⟨ε, hε, fun t h2 h3 => ?_, fun t h2 h3 => ?_⟩
  · have := ha t h2 h3; simp only [h1] at this; exact this
  · have := hb t h2 h3; simp only [h1] at this; exact this

lemma H_zero_lt_one (hS : IsStrictlyStarShapedLevel H) : H 0 < 1 := by
  have hne : H 0 ≠ 1 := fun h => by have := hS.2.2 0 h; simp at this
  rcases lt_or_gt_of_ne hne with h | h
  · exact h
  exfalso
  set u : R4 := Pi.single 0 1
  have hu : u ≠ 0 := by
    intro h0; have := congrFun h0 0; simp [u] at this
  obtain ⟨r, ⟨hr, h1⟩, huniq⟩ := hS.2.1 u hu
  obtain ⟨ε, hε, -, hb⟩ := ray_cross hS hr h1
  set t := max (r - ε / 2) (r / 2)
  have ht0 : 0 < t := lt_max_of_lt_right (by linarith)
  have htr : t < r := max_lt (by linarith) (by linarith)
  have hft : H (t • u) < 1 := hb t (lt_max_of_lt_left (by linarith)) htr
  have hcont := (continuous_ray hS.1 u).continuousOn (s := Set.Icc 0 t)
  obtain ⟨s, ⟨hs0, hst⟩, hs1⟩ := intermediate_value_Ioo' ht0.le hcont
    (show (1 : ℝ) ∈ Set.Ioo (H (t • u)) (H ((0 : ℝ) • u)) by simp; exact ⟨hft, h⟩)
  have := huniq s ⟨hs0, hs1⟩
  linarith

/-- The unique crossing radius on a ray is the only point where `H = 1`. -/
lemma ray_crossing_lt (hS : IsStrictlyStarShapedLevel H) {w : R4} (hw : w ≠ 0) {s : ℝ}
    (hs : 0 < s) (h1 : 1 < H (s • w)) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : H (ρ • w) = 1) : ρ < s := by
  obtain ⟨r, -, huniq⟩ := hS.2.1 w hw
  have hcont := (continuous_ray hS.1 w).continuousOn (s := Set.Icc 0 s)
  obtain ⟨t, ⟨ht0, hts⟩, ht1⟩ := intermediate_value_Ioo hs.le hcont
    (show (1 : ℝ) ∈ Set.Ioo (H ((0 : ℝ) • w)) (H (s • w)) by
      simp; exact ⟨H_zero_lt_one hS, h1⟩)
  have e1 := huniq t ⟨ht0, ht1⟩
  have e2 := huniq ρ ⟨hρ, hρ1⟩
  linarith

lemma energySurface_isBounded (hS : IsStrictlyStarShapedLevel H) :
    Bornology.IsBounded (energySurface H) := by
  by_contra hb
  rw [isBounded_iff_forall_norm_le] at hb
  push Not at hb
  have hx : ∀ n : ℕ, ∃ x ∈ energySurface H, (n : ℝ) < ‖x‖ := fun n => hb n
  choose x hxS hxn using hx
  have hx0 : ∀ n, x n ≠ 0 := fun n h => by
    have := hxn n; rw [h, norm_zero] at this; exact absurd this (not_lt.2 n.cast_nonneg)
  set u : ℕ → R4 := fun n => ‖x n‖⁻¹ • x n
  have hu : ∀ n, u n ∈ Metric.sphere (0 : R4) 1 := fun n => by
    simp [u, norm_smul, hx0 n]
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere (0 : R4) 1).tendsto_subseq hu
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  obtain ⟨r, ⟨hr, h1⟩, -⟩ := hS.2.1 v hv0
  obtain ⟨ε, hε, ha, -⟩ := ray_cross hS hr h1
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = r + ε / 2 := ⟨_, rfl⟩
  have hs1 : 1 < H (s • v) := ha s (by rw [hs_def]; linarith) (by rw [hs_def]; linarith)
  have hs0 : 0 < s := by rw [hs_def]; linarith
  -- eventually `H (s • u (φ j)) > 1`
  have hc : Tendsto (fun j => H (s • u (φ j))) atTop (𝓝 (H (s • v))) :=
    ((hS.1.continuous.comp (continuous_const_smul s)).tendsto v).comp hlim
  have hev1 : ∀ᶠ j in atTop, 1 < H (s • u (φ j)) := hc.eventually (lt_mem_nhds hs1)
  have hev2 : ∀ᶠ j in atTop, s < ‖x (φ j)‖ := by
    obtain ⟨N, hN⟩ := exists_nat_gt s
    filter_upwards [eventually_ge_atTop N] with j hj
    have := hxn (φ j)
    have : (N : ℝ) ≤ φ j := by exact_mod_cast hj.trans (hφ.id_le j)
    linarith
  obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
  have hn0 : 0 < ‖x (φ j)‖ := norm_pos_iff.2 (hx0 _)
  have hw0 : u (φ j) ≠ 0 := by
    intro h; have := hu (φ j); rw [h] at this; simp at this
  have hρ1 : H (‖x (φ j)‖ • u (φ j)) = 1 := by
    simp only [u, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]; exact hxS _
  have := ray_crossing_lt hS hw0 hs0 hj1 hn0 hρ1
  linarith

lemma energySurface_isCompact (hS : IsStrictlyStarShapedLevel H) :
    IsCompact (energySurface H) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_eq hS.1.continuous continuous_const)
    (energySurface_isBounded hS)

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### A uniform constant `k` -/

lemma hess_add_scale (L : R4 →L[ℝ] R4 →L[ℝ] ℝ) (l : R4 →L[ℝ] ℝ) (c : ℝ) (v : R4) :
    L (c • v) (c • v) = c ^ 2 * L v v ∧ l (c • v) ^ 2 = c ^ 2 * l v ^ 2 := by
  constructor
  · simp [map_smul, smul_eq_mul]; ring
  · simp [map_smul, smul_eq_mul]; ring

/-- On a strictly convex star-shaped level there is `k > 0` with
`D²H(x)(v,v) + k (dH(x) v)² > 0` for all `x ∈ S`, `v ≠ 0`. -/
lemma exists_uniform_k (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H) :
    ∃ k > 0, ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) x v v + k * fderiv ℝ H x v ^ 2 := by
  by_contra hneg
  push Not at hneg
  have hseq : ∀ n : ℕ, ∃ p : R4 × R4, p ∈ energySurface H ×ˢ Metric.sphere (0 : R4) 1 ∧
      fderiv ℝ (fderiv ℝ H) p.1 p.2 p.2 + ((n : ℝ) + 1) * fderiv ℝ H p.1 p.2 ^ 2 ≤ 0 := by
    intro n
    obtain ⟨x, hx, v, hv, hle⟩ := hneg ((n : ℝ) + 1) (by positivity)
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine ⟨(x, ‖v‖⁻¹ • v), ⟨hx, by simp [norm_smul, hn.ne']⟩, ?_⟩
    obtain ⟨e1, e2⟩ := hess_add_scale (fderiv ℝ (fderiv ℝ H) x) (fderiv ℝ H x) ‖v‖⁻¹ v
    simp only
    rw [e1, e2]
    have : ‖v‖⁻¹ ^ 2 * (fderiv ℝ (fderiv ℝ H) x v v + ((n : ℝ) + 1) * fderiv ℝ H x v ^ 2)
        ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  choose p hpK hple using hseq
  have hK : IsCompact (energySurface H ×ˢ Metric.sphere (0 : R4) 1) :=
    (energySurface_isCompact hS).prod (isCompact_sphere 0 1)
  obtain ⟨q, hq, φ, hφ, hlim⟩ := hK.tendsto_subseq hpK
  -- continuous quantities
  have hq2 : Continuous fun p : R4 × R4 => fderiv ℝ (fderiv ℝ H) p.1 p.2 p.2 :=
    (((contDiff_fderiv2_of_smooth hS.1).continuous.comp continuous_fst).clm_apply
      continuous_snd).clm_apply continuous_snd
  have hq1 : Continuous fun p : R4 × R4 => fderiv ℝ H p.1 p.2 :=
    ((contDiff_fderiv_of_smooth hS.1).continuous.comp continuous_fst).clm_apply continuous_snd
  have tQ := (hq2.tendsto q).comp hlim
  have tA := ((hq1.tendsto q).pow 2).comp hlim
  have hQn : ∀ j, fderiv ℝ (fderiv ℝ H) (p (φ j)).1 (p (φ j)).2 (p (φ j)).2 ≤ 0 := fun j => by
    have := hple (φ j); nlinarith [sq_nonneg (fderiv ℝ H (p (φ j)).1 (p (φ j)).2)]
  have hQ : fderiv ℝ (fderiv ℝ H) q.1 q.2 q.2 ≤ 0 :=
    le_of_tendsto' tQ fun j => hQn j
  -- `(dH v)² ≤ -Q / (n + 1) → 0`
  have tInv : Tendsto (fun j => ((φ j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => (φ j : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1
        (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    exact h1.inv_tendsto_atTop
  have tB : Tendsto (fun j => -fderiv ℝ (fderiv ℝ H) (p (φ j)).1 (p (φ j)).2 (p (φ j)).2 *
      ((φ j : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa using tQ.neg.mul tInv
  have hA : fderiv ℝ H q.1 q.2 ^ 2 ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tA tB fun j => ?_
    have := hple (φ j)
    have hpos : (0 : ℝ) < (φ j : ℝ) + 1 := by positivity
    simp only [Function.comp_apply]
    rw [le_mul_inv_iff₀ hpos]
    linarith
  have hA0 : fderiv ℝ H q.1 q.2 = 0 := by nlinarith [sq_nonneg (fderiv ℝ H q.1 q.2)]
  have hq0 : q.2 ≠ 0 := by
    intro h; have := hq.2; rw [h] at this; simp at this
  have := hC q.1 hq.1 q.2 hq0 hA0
  linarith

/-! ### The model Hamiltonian `G = exp (k (H - 1))` -/

lemma hasFDerivAt_G (hH : ContDiff ℝ ∞ H) (k : ℝ) (y : R4) :
    HasFDerivAt (fun y => Real.exp (k * (H y - 1)))
      ((Real.exp (k * (H y - 1)) * k) • fderiv ℝ H y) y := by
  have hd : HasFDerivAt H (fderiv ℝ H y) y :=
    (hH.differentiable (by simp) y).hasFDerivAt
  have he : HasFDerivAt (fun y => k * (H y - 1)) (k • fderiv ℝ H y) y := by
    have := (hd.sub (hasFDerivAt_const (1 : ℝ) y)).const_mul k
    simpa using this
  refine he.exp.congr_fderiv ?_
  rw [smul_smul]

lemma fderiv_G (hH : ContDiff ℝ ∞ H) (k : ℝ) :
    fderiv ℝ (fun y => Real.exp (k * (H y - 1))) =
      fun y => (Real.exp (k * (H y - 1)) * k) • fderiv ℝ H y :=
  funext fun y => (hasFDerivAt_G hH k y).fderiv

lemma fderiv2_G_apply (hH : ContDiff ℝ ∞ H) (k : ℝ) {y : R4} (hy : H y = 1) (w v : R4) :
    fderiv ℝ (fderiv ℝ (fun y => Real.exp (k * (H y - 1)))) y w v =
      k * fderiv ℝ (fderiv ℝ H) y w v + k * k * fderiv ℝ H y w * fderiv ℝ H y v := by
  rw [fderiv_G hH k]
  have hd : HasFDerivAt H (fderiv ℝ H y) y :=
    (hH.differentiable (by simp) y).hasFDerivAt
  have hc : HasFDerivAt (fun y => Real.exp (k * (H y - 1)) * k)
      (k • ((Real.exp (k * (H y - 1)) * k) • fderiv ℝ H y)) y :=
    (hasFDerivAt_G hH k y).mul_const k
  have hf : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) y) y :=
    ((contDiff_fderiv_of_smooth hH).differentiable (by simp) y).hasFDerivAt
  have h2 : fderiv ℝ (fun y => (Real.exp (k * (H y - 1)) * k) • fderiv ℝ H y) y = _ :=
    (hc.smul hf).fderiv
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, hy, sub_self, mul_zero, Real.exp_zero, one_mul,
    smul_eq_mul]
  ring

lemma G_eq_one_iff {k : ℝ} (hk : 0 < k) (y : R4) :
    Real.exp (k * (H y - 1)) = 1 ↔ H y = 1 := by
  rw [Real.exp_eq_one_iff, mul_eq_zero, sub_eq_zero]
  exact ⟨fun h => h.resolve_left hk.ne', Or.inr⟩

lemma fderiv_G_of_mem (hH : ContDiff ℝ ∞ H) (k : ℝ) {y : R4} (hy : H y = 1) :
    fderiv ℝ (fun y => Real.exp (k * (H y - 1))) y = k • fderiv ℝ H y := by
  rw [fderiv_G hH k]; simp [hy]

lemma hvf_G_of_mem (hH : ContDiff ℝ ∞ H) (k : ℝ) {y : R4} (hy : H y = 1) :
    hamiltonianVectorField (fun y => Real.exp (k * (H y - 1))) y =
      k • hamiltonianVectorField H y := by
  rw [hamiltonianVectorField_eq, hamiltonianVectorField_eq]
  simp only
  rw [fderiv_G_of_mem hH k hy, map_smul]

lemma fderiv_hvf_G_apply (hH : ContDiff ℝ ∞ H) (k : ℝ) {y : R4} (hy : H y = 1) (w : R4) :
    fderiv ℝ (hamiltonianVectorField (fun y => Real.exp (k * (H y - 1)))) y w =
      k • fderiv ℝ (hamiltonianVectorField H) y w +
        (k * k * fderiv ℝ H y w) • hamiltonianVectorField H y := by
  have hG : ContDiff ℝ ∞ (fun y => Real.exp (k * (H y - 1))) :=
    (contDiff_const.mul (hH.sub contDiff_const)).exp
  rw [fderiv_hvf hG, fderiv_hvf hH, hamiltonianVectorField_eq]
  simp only [ContinuousLinearMap.comp_apply]
  have : fderiv ℝ (fderiv ℝ (fun y => Real.exp (k * (H y - 1)))) y w =
      k • fderiv ℝ (fderiv ℝ H) y w + (k * k * fderiv ℝ H y w) • fderiv ℝ H y := by
    ext v; rw [fderiv2_G_apply hH k hy]; simp [smul_eq_mul]
  rw [this, map_add, map_smul, map_smul]

end HryniewiczCriterion

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

lemma liouvilleForm_smul_right (y v : R4) (c : ℝ) :
    liouvilleForm y (c • v) = c * liouvilleForm y v := by
  simp [liouvilleForm]; ring

lemma xiFrameRaw_G (hH : ContDiff ℝ ∞ H) {k : ℝ} (hk : 0 < k) {y : R4} (hy : H y = 1)
    (Q : R4 → R4) :
    xiFrameRaw (fun y => Real.exp (k * (H y - 1))) Q y = xiFrameRaw H Q y := by
  simp only [xiFrameRaw, fderiv_G_of_mem hH k hy, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hk.ne']

lemma xiFrame1_G (hH : ContDiff ℝ ∞ H) {k : ℝ} (hk : 0 < k) {y : R4} (hy : H y = 1) :
    xiFrame1 (fun y => Real.exp (k * (H y - 1))) y = xiFrame1 H y := by
  simp only [xiFrame1, xiFrameRaw_G hH hk hy]

lemma xiFrame2_G (hH : ContDiff ℝ ∞ H) {k : ℝ} (hk : 0 < k) {y : R4} (hy : H y = 1) :
    xiFrame2 (fun y => Real.exp (k * (H y - 1))) y = xiFrame2 H y := by
  simp only [xiFrame2, xiFrameRaw_G hH hk hy]

lemma reebProjection_G (hH : ContDiff ℝ ∞ H) {k : ℝ} (hk : 0 < k) {y : R4} (hy : H y = 1)
    (v : R4) :
    reebProjection (fun y => Real.exp (k * (H y - 1))) y v = reebProjection H y v := by
  simp only [reebProjection, hvf_G_of_mem hH k hy, liouvilleForm_smul_right, smul_smul]
  congr 2
  by_cases h : liouvilleForm y (hamiltonianVectorField H y) = 0
  · simp [h]
  · field_simp

theorem exists_ambient_positive_contact_model' (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H) :
    ∃ G : R4 → ℝ, IsStrictlyStarShapedLevel G ∧ energySurface G = energySurface H ∧
      (∀ x : R4, G x = 1 → ∀ v : R4, v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ G) x v v) ∧
      ∀ (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)),
        IsLinearizedFlow H P.x Y →
        ∃ (Q : PeriodicOrbit G) (Z : ℝ → (R4 →L[ℝ] R4)),
          IsLinearizedFlow G Q.x Z ∧
          linearizedXiPath G Q Z = linearizedXiPath H P Y := by
  obtain ⟨k, hk, hkpos⟩ := exists_uniform_k hS hC
  have hH := hS.1
  have hGs : ContDiff ℝ ∞ (fun y => Real.exp (k * (H y - 1))) :=
    (contDiff_const.mul (hH.sub contDiff_const)).exp
  refine ⟨fun y => Real.exp (k * (H y - 1)), ⟨hGs, fun u hu => ?_, fun x hx => ?_⟩, ?_, ?_, ?_⟩
  · simp only [G_eq_one_iff hk]; exact hS.2.1 u hu
  · rw [G_eq_one_iff hk] at hx
    rw [fderiv_G_of_mem hH k hx, ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_pos hk (hS.2.2 x hx)
  · ext y; simp only [energySurface, Set.mem_setOf_eq, G_eq_one_iff hk]
  · intro x hx v hv
    rw [G_eq_one_iff hk] at hx
    rw [fderiv2_G_apply hH k hx]
    have := mul_pos hk (hkpos x hx v hv)
    nlinarith
  intro P Y hY
  have hPx : ∀ t, H (P.x t) = 1 := P.trajectory.2
  have hscale : ∀ t, HasDerivAt (fun t : ℝ => k * t) k t := fun t => by
    simpa using (hasDerivAt_id t).const_mul k
  have hxk : ∀ t, HasDerivAt (fun t => P.x (k * t))
      (k • hamiltonianVectorField H (P.x (k * t))) t := fun t =>
    (P.trajectory.1 (k * t)).scomp t (hscale t)
  have htraj : IsTrajectory (fun y => Real.exp (k * (H y - 1))) (fun t => P.x (k * t)) := by
    refine ⟨fun t => ?_, fun t => (G_eq_one_iff hk _).2 (hPx _)⟩
    rw [hvf_G_of_mem hH k (hPx _)]
    exact hxk t
  let Q : PeriodicOrbit (fun y => Real.exp (k * (H y - 1))) :=
    { x := fun t => P.x (k * t)
      T := P.T / k
      T_pos := div_pos P.T_pos hk
      trajectory := htraj
      periodic := fun t => by
        show P.x (k * (t + P.T / k)) = P.x (k * t)
        rw [mul_add, mul_div_cancel₀ _ hk.ne']
        exact P.periodic _ }
  set L : R4 →L[ℝ] ℝ := fderiv ℝ H (P.x 0) with hL
  let Z : ℝ → (R4 →L[ℝ] R4) := fun t =>
    Y (k * t) + (k ^ 2 * t) •
      ContinuousLinearMap.smulRightL ℝ R4 R4 L (hamiltonianVectorField H (P.x (k * t)))
  have hZ : IsLinearizedFlow (fun y => Real.exp (k * (H y - 1))) Q.x Z := by
    refine ⟨?_, fun t => ?_⟩
    · simp [Z, hY.1]
    have dY : HasDerivAt (fun t => Y (k * t))
        (k • (fderiv ℝ (hamiltonianVectorField H) (P.x (k * t))).comp (Y (k * t))) t :=
      (hY.2 (k * t)).scomp t (hscale t)
    have dX : HasDerivAt (fun t => hamiltonianVectorField H (P.x (k * t)))
        (fderiv ℝ (hamiltonianVectorField H) (P.x (k * t))
          (k • hamiltonianVectorField H (P.x (k * t)))) t := by
      have := (hasFDerivAt_hvf hH (P.x (k * t))).comp_hasDerivAt t (hxk t)
      rw [← fderiv_hvf hH] at this
      exact this
    have dS := (ContinuousLinearMap.smulRightL ℝ R4 R4 L).hasFDerivAt.comp_hasDerivAt t dX
    have dc : HasDerivAt (fun t : ℝ => k ^ 2 * t) (k ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (k ^ 2)
    have dZ := dY.add (dc.smul dS)
    refine dZ.congr_deriv ?_
    ext w i
    have hdY : fderiv ℝ H (P.x (k * t)) (Y (k * t) w) = L w := by
      rw [dH_linearizedFlow hH P.trajectory hY]
    have hdX : fderiv ℝ H (P.x (k * t)) (hamiltonianVectorField H (P.x (k * t))) = 0 := by
      rw [hamiltonianVectorField_eq]; exact apply_jvec_self _
    simp only [Q, Z, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Function.comp_apply,
      ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply]
    rw [fderiv_hvf_G_apply hH k (hPx _) _]
    simp only [map_add, map_smul, hdY, hdX, smul_eq_mul, Pi.add_apply, Pi.smul_apply, mul_zero,
      zero_mul, add_zero]
    ring
  refine ⟨Q, Z, hZ, ?_⟩
  -- the two matrix paths coincide
  have hpos0 : 0 < fderiv ℝ H (P.x 0) (P.x 0) := hS.2.2 _ (hPx 0)
  have hLE : ∀ j : Fin 2, L (![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] j) = 0 := by
    intro j
    fin_cases j <;> simp [hL, xiFrame1, xiFrame2, map_smul, dH_xiFrameRaw hpos0]
  funext τ
  ext i j
  have hpt : k * (P.T / k * τ) = P.T * τ := by field_simp
  simp only [linearizedXiPath, Matrix.of_apply, Q, Z, hpt, mul_zero,
    xiFrame1_G hH hk (hPx _), xiFrame2_G hH hk (hPx _), xiCoords,
    reebProjection_G hH hk (hPx _), ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, hLE,
    zero_smul, smul_zero, add_zero]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H) :
    ∃ G : R4 → ℝ, IsStrictlyStarShapedLevel G ∧ energySurface G = energySurface H ∧
      (∀ x : R4, G x = 1 → ∀ v : R4, v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ G) x v v) ∧
      ∀ (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)),
        IsLinearizedFlow H P.x Y →
        ∃ (Q : PeriodicOrbit G) (Z : ℝ → (R4 →L[ℝ] R4)),
          IsLinearizedFlow G Q.x Z ∧
          linearizedXiPath G Q Z = linearizedXiPath H P Y :=
  exists_ambient_positive_contact_model' H hS hC
