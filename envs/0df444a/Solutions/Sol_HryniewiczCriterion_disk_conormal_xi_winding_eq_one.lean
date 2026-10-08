-- Prove2me | solution 1 for HryniewiczCriterion.disk_conormal_xi_winding_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T18:59:35.758808+00:00
-- url     : https://prove2.me/submissions/47cf57e9-478b-4c3e-b4ab-922b46349160

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open HryniewiczCriterion
open scoped ContDiff
open Complex MeasureTheory Set
open MeasureTheory Set
open Complex
open Complex Set
open scoped ContDiff Topology
open Complex Set MeasureTheory

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
# Winding numbers of `C¹` loops in `ℂ \ {0}` via the logarithmic derivative
-/


noncomputable section

namespace WindA

/-- The log-derivative primitive recovers the loop: `c t = c 0 · exp (∫₀ᵗ c'/c)`. -/
lemma eq_mul_exp_integral {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (t : ℝ) :
    c t = c 0 * exp (∫ s in (0 : ℝ)..t, c' s / c s) := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, c' s / c s
  have hL : ∀ t, HasDerivAt L (c' t / c t) t := fun t =>
    (hq.integral_hasStrictDerivAt 0 t).hasDerivAt
  set g : ℝ → ℂ := fun t => c t * exp (-L t)
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h1 : HasDerivAt g (c' t * exp (-L t) + c t * (exp (-L t) * -(c' t / c t))) t :=
      (hc t).mul (HasDerivAt.cexp (f := fun t => -L t) (hL t).neg)
    convert h1 using 1
    field_simp [hne t]
    ring
  have hconst : ∀ t, g t = g 0 := fun t =>
    is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) t 0
  have hL0 : L 0 = 0 := by simp [L]
  have := hconst t
  simp only [g, hL0, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- The log-derivative integral of a closed `C¹` loop lies in `2πi ℤ`. -/
lemma integral_mem_two_pi_I {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0) :
    ∃ k : ℤ, ∫ s in (0 : ℝ)..1, c' s / c s = k * (2 * Real.pi * I) := by
  have h := eq_mul_exp_integral hc hc' hne 1
  rw [hper] at h
  have h1 : exp (∫ s in (0 : ℝ)..1, c' s / c s) = 1 := by
    have h0 := hne 0
    exact mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm)
  exact Complex.exp_eq_one_iff.1 h1

lemma im_integral {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    (∫ s in a..b, f s).im = ∫ s in a..b, (f s).im :=
  (Complex.imCLM.intervalIntegral_comp_comm (hf.intervalIntegrable a b)).symm

/-- Homotopy invariance of the log-derivative integral. -/
lemma integral_eq_of_homotopy {F F' : ℝ → ℝ → ℂ}
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, HasDerivAt (F r) (F' r s) s)
    (hcF : ContinuousOn (Function.uncurry F) (Icc 0 1 ×ˢ univ))
    (hcF' : ContinuousOn (Function.uncurry F') (Icc 0 1 ×ˢ univ))
    (hne : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, F r s ≠ 0)
    (hper : ∀ r ∈ Icc (0 : ℝ) 1, F r 1 = F r 0) :
    ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
  set p : ℝ → ℝ := fun r => (projIcc (0 : ℝ) 1 zero_le_one r : ℝ)
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI : ∀ r, p r ∈ Icc (0 : ℝ) 1 := fun r => (projIcc (0 : ℝ) 1 zero_le_one r).2
  have hpid : ∀ r ∈ Icc (0 : ℝ) 1, p r = r := fun r hr => by simp [p, projIcc_of_mem _ hr]
  set G : ℝ → ℝ → ℂ := fun r s => F' (p r) s / F (p r) s
  have hmap : Continuous fun q : ℝ × ℝ => (p q.1, q.2) := (hp.comp continuous_fst).prodMk continuous_snd
  have hmapI : ∀ q : ℝ × ℝ, (p q.1, q.2) ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) :=
    fun q => ⟨hpI q.1, trivial⟩
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun q : ℝ × ℝ => Function.uncurry F' (p q.1, q.2) :=
      hcF'.comp_continuous hmap hmapI
    have h2 : Continuous fun q : ℝ × ℝ => Function.uncurry F (p q.1, q.2) :=
      hcF.comp_continuous hmap hmapI
    exact h1.div h2 fun q => hne _ (hpI q.1) q.2
  set W : ℝ → ℂ := fun r => ∫ s in (0 : ℝ)..1, G r s
  have hW : Continuous W := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc 0 1
  -- `W r ∈ 2πiℤ`
  have hk : ∀ r, ∃ k : ℤ, W r = k * (2 * Real.pi * I) := by
    intro r
    have hr := hpI r
    have hcont : Continuous (F' (p r)) := by
      have := hGc.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (r, s))
      have h1 : Continuous fun s : ℝ => Function.uncurry F' (p r, s) :=
        hcF'.comp_continuous (continuous_const.prodMk continuous_id) fun s => ⟨hr, trivial⟩
      exact h1
    exact integral_mem_two_pi_I (hF _ hr) hcont (hne _ hr) (hper _ hr)
  set f : ℝ → ℝ := fun r => (W r).im / (2 * Real.pi)
  have hf : Continuous f := (Complex.continuous_im.comp hW).div_const _
  have hfint : ∀ r, ∃ k : ℤ, f r = k := by
    intro r; obtain ⟨k, hk⟩ := hk r
    refine ⟨k, ?_⟩
    simp only [f, hk]
    simp [Complex.mul_im]
  have hWre : ∀ r, W r = (f r : ℂ) * (2 * Real.pi * I) := by
    intro r; obtain ⟨k, hk'⟩ := hk r
    have : f r = k := by
      simp only [f, hk']; simp [Complex.mul_im]
    rw [this, hk']; push_cast; ring
  -- `f` is constant on `[0, 1]`
  obtain ⟨k0, hk0⟩ := hfint 0
  obtain ⟨k1, hk1⟩ := hfint 1
  have hk01 : k0 = k1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · have hmem : (k0 : ℝ) + 1 / 2 ∈ Icc (f 0) (f 1) := by
        rw [hk0, hk1]
        have : (k0 : ℝ) + 1 ≤ k1 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k0 = 1 / 2 := by linarith
      have h2 : ((k - k0 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k0 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k0) : ℤ) = 1 := by exact_mod_cast h3
      omega
    · have hmem : (k1 : ℝ) + 1 / 2 ∈ Icc (f 1) (f 0) := by
        rw [hk0, hk1]
        have : (k1 : ℝ) + 1 ≤ k0 := by exact_mod_cast h
        constructor <;> linarith
      obtain ⟨r, -, hr⟩ := intermediate_value_Icc' zero_le_one hf.continuousOn hmem
      obtain ⟨k, hk⟩ := hfint r
      rw [hk] at hr
      have h1 : (k : ℝ) - k1 = 1 / 2 := by linarith
      have h2 : ((k - k1 : ℤ) : ℝ) = 1 / 2 := by push_cast; exact h1
      have h3 : (2 : ℝ) * ((k - k1 : ℤ) : ℝ) = 1 := by rw [h2]; norm_num
      have h4 : (2 * (k - k1) : ℤ) = 1 := by exact_mod_cast h3
      omega
  have hW1 : W 1 = W 0 := by rw [hWre 1, hWre 0, hk0, hk1, hk01]
  have e1 : W 1 = ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s := by
    simp only [W, G, hpid 1 ⟨zero_le_one, le_rfl⟩]
  have e0 : W 0 = ∫ s in (0 : ℝ)..1, F' 0 s / F 0 s := by
    simp only [W, G, hpid 0 ⟨le_rfl, zero_le_one⟩]
  rw [← e1, ← e0, hW1]

/-- A closed loop whose argument strictly increases and which returns to the ray of
`c 0` only at the ends winds exactly once. -/
lemma integral_eq_two_pi_I_of_im_pos {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t)
    (hc' : Continuous c') (hne : ∀ t, c t ≠ 0) (hper : c 1 = c 0)
    (hpos : ∀ t, 0 < (c' t / c t).im)
    (hray : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c t ≠ (l : ℂ) * c 0) :
    ∫ s in (0 : ℝ)..1, c' s / c s = 2 * Real.pi * I := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  have hq : Continuous fun s => c' s / c s := hc'.div hcc hne
  obtain ⟨k, hk⟩ := integral_mem_two_pi_I hc hc' hne hper
  set θ : ℝ → ℝ := fun t => (∫ s in (0 : ℝ)..t, c' s / c s).im
  have hθ : ∀ t, θ t = ∫ s in (0 : ℝ)..t, (c' s / c s).im := fun t => im_integral hq 0 t
  have hθc : Continuous θ := by
    have : θ = fun t => ∫ s in (0 : ℝ)..t, (c' s / c s).im := funext hθ
    rw [this]
    exact continuous_iff_continuousAt.2 fun t =>
      ((Complex.continuous_im.comp hq).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  have hθ1 : θ 1 = 2 * Real.pi * k := by
    simp only [θ, hk]; simp [Complex.mul_im]; ring
  have hθ1pos : 0 < θ 1 := by
    rw [hθ]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Complex.continuous_im.comp hq).intervalIntegrable 0 1) (fun t _ => hpos t) zero_lt_one
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by
      rw [hθ1] at hθ1pos
      have := Real.pi_pos
      nlinarith
    exact_mod_cast this
  have hk1 : k = 1 := by
    by_contra hk1
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show (2 : ℤ) ≤ k by omega)
    have hθ0 : θ 0 = 0 := by simp [θ]
    have hmem : 2 * Real.pi ∈ Icc (θ 0) (θ 1) := by
      rw [hθ0, hθ1]
      have := Real.pi_pos
      constructor <;> nlinarith
    obtain ⟨t, ht, hθt⟩ := intermediate_value_Icc zero_le_one hθc.continuousOn hmem
    have ht0 : t ≠ 0 := by
      rintro rfl; rw [hθ0] at hθt; have := Real.pi_pos; linarith
    have ht1 : t ≠ 1 := by
      rintro rfl; rw [hθ1] at hθt; have := Real.pi_pos; nlinarith
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    set L := ∫ s in (0 : ℝ)..t, c' s / c s
    have hL : L = (L.re : ℂ) + (2 * Real.pi : ℝ) * I := by
      apply Complex.ext <;> simp [θ] at hθt ⊢
      first | exact hθt | exact hθt.symm
    have hct := eq_mul_exp_integral hc hc' hne t
    apply hray t htI (Real.exp L.re) (Real.exp_pos _)
    have h2 : exp (((2 * Real.pi : ℝ) : ℂ) * I) = 1 := by
      push_cast; exact Complex.exp_two_pi_mul_I
    have hE : exp L = (Real.exp L.re : ℂ) := by
      conv_lhs => rw [hL]
      rw [Complex.exp_add, h2, mul_one, Complex.ofReal_exp]
    rw [hct, hE]; ring
  rw [hk, hk1]; simp

end WindA

/-!
# Smooth polar lifts of loops, Fubini for continuous integrands, and the action identity
-/


noncomputable section

namespace WindA

/-- Fubini on `[0,1]²` for a continuous integrand. -/
lemma integral_integral_swap_unit {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f x y = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f x y := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- A smooth closed loop in `ℂ \ {0}` with winding number one has a smooth polar form
`c = r e^{iθ}` with `r > 0` periodic and `θ(s + 1) = θ(s) + 2π`. -/
lemma exists_polar_of_winding_one {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hne : ∀ s, c s ≠ 0)
    (hper : ∀ s, c (s + 1) = c s)
    (hW : ∫ s in (0 : ℝ)..1, deriv c s / c s = 2 * Real.pi * I) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧
      (∀ s, r (s + 1) = r s) ∧ (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := by
  have hd : ∀ t, HasDerivAt c (deriv c t) t := fun t =>
    ((hc.differentiable (by simp)) t).hasDerivAt
  have hdc : ContDiff ℝ ∞ (deriv c) := hc.iterate_deriv 1
  have hq : ContDiff ℝ ∞ fun s => deriv c s / c s := by
    simp only [div_eq_mul_inv]; exact hdc.mul (hc.inv hne)
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, deriv c s / c s
  have hL : ∀ t, HasDerivAt L (deriv c t / c t) t := fun t =>
    (hq.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hLs : ContDiff ℝ ∞ L :=
    HryniewiczCriterion.contDiff_of_hasDerivAt hL fun n _ => hq.of_le (by exact_mod_cast le_top)
  have hexp := eq_mul_exp_integral hd hdc.continuous hne
  set r : ℝ → ℝ := fun s => ‖c 0‖ * Real.exp (L s).re
  set θ : ℝ → ℝ := fun s => arg (c 0) + (L s).im
  have hexp' : ∀ t, c t = c 0 * exp (L t) := hexp
  have hpolar : ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := by
    intro s
    have e1 : exp (L s) = (Real.exp (L s).re : ℂ) * exp (((L s).im : ℂ) * I) := by
      conv_lhs => rw [← Complex.re_add_im (L s)]
      rw [Complex.exp_add, Complex.ofReal_exp]
    have e2 := norm_mul_exp_arg_mul_I (c 0)
    rw [← Complex.exp_ofReal_mul_I, hexp' s, e1]
    conv_lhs => rw [← e2]
    simp only [r, θ]
    push_cast
    rw [show ((arg (c 0) : ℂ) + ((L s).im : ℂ)) * I = (arg (c 0) : ℂ) * I + ((L s).im : ℂ) * I by ring,
      Complex.exp_add]
    ring
  have hrpos : ∀ s, 0 < r s := fun s => mul_pos (norm_pos_iff.2 (hne 0)) (Real.exp_pos _)
  have hnorm : ∀ s, ‖c s‖ = r s := by
    intro s
    rw [hpolar s, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hrpos s).le,
      ← Complex.exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hqper : Function.Periodic (fun s => deriv c s / c s) 1 := by
    intro s
    have : deriv c (s + 1) = deriv c s := by
      have h1 : (fun t => c (t + 1)) = c := funext hper
      have := deriv_comp_add_const (f := c) (a := 1) (x := s)
      rw [h1] at this; exact this.symm
    simp only [this, hper]
  have hLper : ∀ s, L (s + 1) = L s + 2 * Real.pi * I := by
    intro s
    have := hqper.intervalIntegral_add_eq_add 0 s (fun a b => hq.continuous.intervalIntegrable a b)
    simp only [zero_add] at this
    simp only [L]; rw [this, hW]
  refine ⟨r, θ, ?_, ?_, hrpos, ?_, ?_, hpolar⟩
  · exact contDiff_const.mul (Real.contDiff_exp.comp (Complex.reCLM.contDiff.comp hLs))
  · exact contDiff_const.add (Complex.imCLM.contDiff.comp hLs)
  · intro s; rw [← hnorm, ← hnorm, hper]
  · intro s; simp only [θ, hLper]; simp; ring

end WindA

/-!
# The action identity `∫_{∂D} ω₀(c, ∂ₛc) = 2 ∬ ω₀(∂ᵣc, ∂ₛc)` for a family of loops
-/


noncomputable section

namespace HryniewiczCriterion

lemma hasDerivAt_omega0 {f g : ℝ → R4} {f' g' : R4} {t : ℝ} (hf : HasDerivAt f f' t)
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun t => omega0 (f t) (g t)) (omega0 f' (g t) + omega0 (f t) g') t := by
  have hfi := fun i => (hasDerivAt_pi.1 hf) i
  have hgi := fun i => (hasDerivAt_pi.1 hg) i
  have h := ((((hfi 0).mul (hgi 1)).sub ((hfi 1).mul (hgi 0))).add ((hfi 2).mul (hgi 3))).sub
    ((hfi 3).mul (hgi 2))
  convert h using 1 <;> first | rfl | (simp only [omega0]; ring) | (funext t; simp only [omega0]) | skip

lemma continuous_omega0 {X : Type*} [TopologicalSpace X] {f g : X → R4} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => omega0 (f x) (g x) := by
  have hfi := fun i => (continuous_apply i).comp hf
  have hgi := fun i => (continuous_apply i).comp hg
  simp only [omega0]
  exact ((((hfi 0).mul (hgi 1)).sub ((hfi 1).mul (hgi 0))).add ((hfi 2).mul (hgi 3))).sub
    ((hfi 3).mul (hgi 2))

/-- The action identity for a smooth family of loops `c r` (`r ∈ [0,1]`), closed in `s`,
starting from a constant loop. -/
theorem action_identity {c : ℝ → ℝ → R4} (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hper : ∀ r, c r 1 = c r 0) (h0 : ∀ s, c 0 s = c 0 0) :
    ∫ s in (0 : ℝ)..1, omega0 (c 1 s) (fderiv ℝ (Function.uncurry c) (1, s) (0, 1)) =
      2 * ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        omega0 (fderiv ℝ (Function.uncurry c) (r, s) (1, 0))
          (fderiv ℝ (Function.uncurry c) (r, s) (0, 1)) := by
  set Φ := Function.uncurry c with hΦ
  set D := fderiv ℝ Φ
  set D2 := fderiv ℝ D
  have hD : ContDiff ℝ ∞ D := hc.fderiv_right le_rfl
  have hD2 : ContDiff ℝ ∞ D2 := hD.fderiv_right le_rfl
  have hΦd : ∀ p, HasFDerivAt Φ (D p) p := fun p => ((hc.differentiable (by simp)) p).hasFDerivAt
  have hDd : ∀ p, HasFDerivAt D (D2 p) p := fun p => ((hD.differentiable (by simp)) p).hasFDerivAt
  have hsymm : ∀ p v w, D2 p v w = D2 p w v := fun p v w =>
    hc.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 le_top) v w
  set e1 : ℝ × ℝ := (1, 0)
  set e2 : ℝ × ℝ := (0, 1)
  have lr : ∀ r s : ℝ, HasDerivAt (fun r => ((r, s) : ℝ × ℝ)) e1 r := fun r s =>
    (hasDerivAt_id r).prodMk (hasDerivAt_const r s)
  have ls : ∀ r s : ℝ, HasDerivAt (fun s => ((r, s) : ℝ × ℝ)) e2 s := fun r s =>
    (hasDerivAt_const s r).prodMk (hasDerivAt_id s)
  have cr : ∀ r s, HasDerivAt (fun r => c r s) (D (r, s) e1) r := fun r s =>
    HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun r => ((r, s) : ℝ × ℝ)) r (hΦd (r, s)) (lr r s)
  have cs : ∀ r s, HasDerivAt (fun s => c r s) (D (r, s) e2) s := fun r s =>
    HasFDerivAt.comp_hasDerivAt (l := Φ) (f := fun s => ((r, s) : ℝ × ℝ)) s (hΦd (r, s)) (ls r s)
  have Dr : ∀ r s v, HasDerivAt (fun r => D (r, s) v) (D2 (r, s) e1 v) r := fun r s v =>
    (ContinuousLinearMap.apply ℝ R4 v).hasFDerivAt.comp_hasDerivAt r
      (HasFDerivAt.comp_hasDerivAt (l := D) (f := fun r => ((r, s) : ℝ × ℝ)) r (hDd (r, s)) (lr r s))
  have Ds : ∀ r s v, HasDerivAt (fun s => D (r, s) v) (D2 (r, s) e2 v) s := fun r s v =>
    (ContinuousLinearMap.apply ℝ R4 v).hasFDerivAt.comp_hasDerivAt s
      (HasFDerivAt.comp_hasDerivAt (l := D) (f := fun s => ((r, s) : ℝ × ℝ)) s (hDd (r, s)) (ls r s))
  -- continuity
  have hcc : Continuous Φ := hc.continuous
  have hDv : ∀ v, Continuous fun p => D p v := fun v => hD.continuous.clm_apply continuous_const
  have hD2v : ∀ v w, Continuous fun p => D2 p v w := fun v w =>
    (hD2.continuous.clm_apply continuous_const).clm_apply continuous_const
  set A : ℝ → ℝ → ℝ := fun r s => omega0 (D (r, s) e1) (D (r, s) e2)
  set B : ℝ → ℝ → ℝ := fun r s => omega0 (c r s) (D2 (r, s) e1 e2)
  have hA : Continuous (Function.uncurry A) := continuous_omega0 (hDv e1) (hDv e2)
  have hB : Continuous (Function.uncurry B) := continuous_omega0 hcc (hD2v e1 e2)
  have hAr : ∀ s, Continuous fun r => A r s := fun s =>
    hA.comp (continuous_id.prodMk continuous_const)
  have hBr : ∀ s, Continuous fun r => B r s := fun s =>
    hB.comp (continuous_id.prodMk continuous_const)
  have hAs : ∀ r, Continuous fun s => A r s := fun r =>
    hA.comp (continuous_const.prodMk continuous_id)
  have hBs : ∀ r, Continuous fun s => B r s := fun r =>
    hB.comp (continuous_const.prodMk continuous_id)
  -- slices in `r`
  have hDe2zero : ∀ s, D (0, s) e2 = 0 := by
    intro s
    have h := cs 0 s
    have hconst : (fun s => c 0 s) = fun _ => c 0 0 := funext h0
    rw [hconst] at h
    exact h.unique (hasDerivAt_const s _)
  have I1 : ∀ s, ∫ r in (0 : ℝ)..1, (A r s + B r s) = omega0 (c 1 s) (D (1, s) e2) := by
    intro s
    have hder : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => omega0 (c r s) (D (r, s) e2))
        (A r s + B r s) r := fun r _ => hasDerivAt_omega0 (cr r s) (Dr r s e2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (((hAr s).add (hBr s)).intervalIntegrable 0 1), hDe2zero]
    simp [omega0]
  have hDe1per : ∀ r, D (r, 1) e1 = D (r, 0) e1 := by
    intro r
    have h1 := cr r 1
    have hfun : (fun r => c r 1) = fun r => c r 0 := funext hper
    rw [hfun] at h1
    exact h1.unique (cr r 0)
  have I2 : ∀ r, ∫ s in (0 : ℝ)..1, (-A r s + B r s) = 0 := by
    intro r
    have hder : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => omega0 (c r s) (D (r, s) e1))
        (-A r s + B r s) s := by
      intro s _
      have h := hasDerivAt_omega0 (cs r s) (Ds r s e1)
      convert h using 1
      simp only [A, B, hsymm (r, s) e2 e1, omega0_antisymm (D (r, s) e2)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (((hAs r).neg.add (hBs r)).intervalIntegrable 0 1), hper, hDe1per, sub_self]
  -- Fubini
  have hswap := WindA.integral_integral_swap_unit (f := fun r s => -A r s + B r s)
    ((hA.neg).add hB)
  simp only [I2, intervalIntegral.integral_zero] at hswap
  have hpar : ∀ {F : ℝ → ℝ → ℝ}, Continuous (Function.uncurry F) →
      Continuous fun s => ∫ r in (0 : ℝ)..1, F r s := by
    intro F hF
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun s r => F r s) (hF.comp continuous_swap) 0 1
  have key : ∀ s, (∫ r in (0 : ℝ)..1, (A r s + B r s)) - ∫ r in (0 : ℝ)..1, (-A r s + B r s) =
      2 * ∫ r in (0 : ℝ)..1, A r s := by
    intro s
    have h := intervalIntegral.integral_sub (μ := volume) (a := 0) (b := 1)
      (f := fun r => A r s + B r s) (g := fun r => -A r s + B r s)
      (((hAr s).add (hBr s)).intervalIntegrable 0 1) (((hAr s).neg.add (hBr s)).intervalIntegrable 0 1)
    refine h.symm.trans ?_
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r; ring
  calc ∫ s in (0 : ℝ)..1, omega0 (c 1 s) (D (1, s) e2)
      = ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, (A r s + B r s) := by simp only [I1]
    _ = (∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, (A r s + B r s)) -
          ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, (-A r s + B r s) := by rw [← hswap, sub_zero]
    _ = ∫ s in (0 : ℝ)..1, ((∫ r in (0 : ℝ)..1, (A r s + B r s)) -
          ∫ r in (0 : ℝ)..1, (-A r s + B r s)) := by
        exact (intervalIntegral.integral_sub
          ((hpar (F := fun r s => A r s + B r s) (hA.add hB)).intervalIntegrable 0 1)
          ((hpar (F := fun r s => -A r s + B r s) (hA.neg.add hB)).intervalIntegrable 0 1)).symm
    _ = ∫ s in (0 : ℝ)..1, 2 * ∫ r in (0 : ℝ)..1, A r s := by simp only [key]
    _ = _ := by rw [intervalIntegral.integral_const_mul]

end HryniewiczCriterion

/-!
# Complex `ξ`-coordinates of the Reeb projection
-/


noncomputable section

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-- The `(Z₁, Z₂)`-coordinates of the Reeb projection of `w` at `x`, as a complex number. -/
def xiPsi (H : R4 → ℝ) (x w : R4) : ℂ :=
  ⟨omega0 (reebProjection H x w) (xiFrame2 H x), omega0 (xiFrame1 H x) (reebProjection H x w)⟩

lemma reebProjection_eq_xiPsi {x w : R4} (hx : 0 < fderiv ℝ H x x) (hw : fderiv ℝ H x w = 0) :
    reebProjection H x w = (xiPsi H x w).re • xiFrame1 H x + (xiPsi H x w).im • xiFrame2 H x := by
  have h12 := omega0_xiFrame12 hx
  have h1a : omega0 (xiFrame1 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ2 omega0_quatQ2
  have h2a : omega0 (xiFrame2 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ1 omega0_quatQ1
  have h1b : omega0 (xiFrame1 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ2
  have h2b : omega0 (xiFrame2 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ1
  have hab : omega0 x (hamiltonianVectorField H x) ≠ 0 := by rw [omega0_y_X]; exact hx.ne'
  exact eq_frame_of_omega0 _ _ _ _ _ h12 h1a h1b h2a h2b hab (omega0_reeb_y hx w)
    (omega0_reeb_X x w hw)

lemma xiPsi_im_conj_mul {x v w : R4} (hx : 0 < fderiv ℝ H x x) (hv : fderiv ℝ H x v = 0)
    (hw : fderiv ℝ H x w = 0) :
    ((starRingEnd ℂ) (xiPsi H x v) * xiPsi H x w).im = omega0 v w := by
  have h12 := omega0_xiFrame12 hx
  have h1a : omega0 (xiFrame1 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ2 omega0_quatQ2
  have h2a : omega0 (xiFrame2 H x) x = 0 := omega0_xiFrame_y (H := H) quatQ1 omega0_quatQ1
  have h1b : omega0 (xiFrame1 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ2
  have h2b : omega0 (xiFrame2 H x) (hamiltonianVectorField H x) = 0 := omega0_xiFrame_X hx quatQ1
  have hab : omega0 x (hamiltonianVectorField H x) ≠ 0 := by rw [omega0_y_X]; exact hx.ne'
  have := omega0_eq_det_of_frame _ _ _ _ _ _ h12 h1a h1b h2a h2b hab (omega0_reeb_y hx v)
    (omega0_reeb_X x v hv) (omega0_reeb_y hx w) (omega0_reeb_X x w hw)
  rw [omega0_reeb_reeb x v w hv hw] at this
  rw [this]
  simp [xiPsi, Complex.mul_im]
  ring

lemma xiPsi_add_smul (x p q : R4) (a b : ℝ) :
    xiPsi H x (a • p + b • q) = (a : ℂ) * xiPsi H x p + (b : ℂ) * xiPsi H x q := by
  apply Complex.ext <;>
  · simp [xiPsi, reebProjection, liouvilleForm, omega0]
    ring

lemma xiPsi_zero (x : R4) : xiPsi H x 0 = 0 := by
  apply Complex.ext <;> simp [xiPsi, reebProjection, liouvilleForm, omega0]

/-! ### Smoothness -/

lemma contDiffAt_omega0 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → R4}
    {p : E} (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ContDiffAt ℝ ∞ (fun q => omega0 (f q) (g q)) p := by
  have h := fun i => contDiffAt_pi.1 hf i
  have k := fun i => contDiffAt_pi.1 hg i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub ((h 3).mul (k 2))

lemma contDiff_dot4 : ContDiff ℝ ∞ (fun x : R4 => dot4 x x) := by
  have hid : ContDiff ℝ ∞ (fun x : R4 => x) := contDiff_id
  have h := fun i => contDiff_pi.1 hid i
  simp only [dot4, Fin.sum_univ_four]
  exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add ((h 3).mul (h 3))

lemma contDiffAt_xiFrame (hH : ContDiff ℝ ∞ H) {x : R4} (hx : 0 < fderiv ℝ H x x) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ Q) :
    ContDiffAt ℝ ∞ (fun y => (euclidNorm y)⁻¹ • xiFrameRaw H Q y) x := by
  have hdH := contDiff_fderiv_of_smooth hH
  have hraw : ContDiffAt ℝ ∞ (fun y => xiFrameRaw H Q y) x := by
    have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ H y (Q y)) := hdH.clm_apply hQ
    have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ H y y) := hdH.clm_apply contDiff_id
    exact hQ.contDiffAt.sub ((h1.contDiffAt.div h2.contDiffAt hx.ne').smul contDiffAt_id)
  have hdne : dot4 x x ≠ 0 := (dot4_pos (ne_zero_of_dH_pos hx)).ne'
  have hnorm : ContDiffAt ℝ ∞ (fun y => euclidNorm y) x := contDiff_dot4.contDiffAt.sqrt hdne
  have hnne : euclidNorm x ≠ 0 := fun h => by
    have := euclidNorm_sq x; rw [h] at this; exact hdne (by linarith)
  exact (hnorm.inv hnne).smul hraw

lemma contDiff_quatQ1 : ContDiff ℝ ∞ quatQ1 := by
  have hid : ContDiff ℝ ∞ (fun x : R4 => x) := contDiff_id
  have h := fun i => contDiff_pi.1 hid i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma contDiff_quatQ2 : ContDiff ℝ ∞ quatQ2 := by
  have hid : ContDiff ℝ ∞ (fun x : R4 => x) := contDiff_id
  have h := fun i => contDiff_pi.1 hid i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

/-- `xiPsi` is smooth in `(x, w)` wherever `dH(x) x > 0`. -/
lemma contDiffAt_xiPsi (hH : ContDiff ℝ ∞ H) {x w : R4} (hx : 0 < fderiv ℝ H x x) :
    ContDiffAt ℝ ∞ (fun p : R4 × R4 => xiPsi H p.1 p.2) (x, w) := by
  have hfst : ContDiffAt ℝ ∞ (fun p : R4 × R4 => p.1) (x, w) := contDiffAt_fst
  have hsnd : ContDiffAt ℝ ∞ (fun p : R4 × R4 => p.2) (x, w) := contDiffAt_snd
  have hZ1 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => xiFrame1 H p.1) (x, w) :=
    ContDiffAt.comp (g := fun y => (euclidNorm y)⁻¹ • xiFrameRaw H quatQ2 y) (x, w)
      (contDiffAt_xiFrame hH hx quatQ2 contDiff_quatQ2) hfst
  have hZ2 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => xiFrame2 H p.1) (x, w) :=
    ContDiffAt.comp (g := fun y => (euclidNorm y)⁻¹ • xiFrameRaw H quatQ1 y) (x, w)
      (contDiffAt_xiFrame hH hx quatQ1 contDiff_quatQ1) hfst
  have hX : ContDiffAt ℝ ∞ (fun p : R4 × R4 => hamiltonianVectorField H p.1) (x, w) :=
    (contDiff_hvf hH).contDiffAt.comp (x, w) hfst
  have hl1 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => liouvilleForm p.1 p.2) (x, w) := by
    simp only [liouvilleForm_eq]; exact (contDiffAt_omega0 hfst hsnd).div_const 2
  have hl2 : ContDiffAt ℝ ∞ (fun p : R4 × R4 => liouvilleForm p.1 (hamiltonianVectorField H p.1))
      (x, w) := by
    simp only [liouvilleForm_eq]; exact (contDiffAt_omega0 hfst hX).div_const 2
  have hne : liouvilleForm x (hamiltonianVectorField H x) ≠ 0 := by
    rw [liouville_X]; exact (half_pos hx).ne'
  have hR : ContDiffAt ℝ ∞ (fun p : R4 × R4 => reebProjection H p.1 p.2) (x, w) :=
    hsnd.sub ((hl1.div hl2 hne).smul hX)
  have ha := contDiffAt_omega0 hR hZ2
  have hb := contDiffAt_omega0 hZ1 hR
  have hc : ContDiffAt ℝ ∞ (fun p : R4 × R4 =>
      (omega0 (reebProjection H p.1 p.2) (xiFrame2 H p.1) : ℂ) +
        (omega0 (xiFrame1 H p.1) (reebProjection H p.1 p.2) : ℂ) * I) (x, w) :=
    (ofRealCLM.contDiff.contDiffAt.comp (x, w) ha).add
      ((ofRealCLM.contDiff.contDiffAt.comp (x, w) hb).mul contDiffAt_const)
  convert hc using 1
  funext p
  apply Complex.ext <;> simp [xiPsi]

end HryniewiczCriterion

/-!
# The disk: tangency, interior non-vanishing of `ξ`-coordinates, sign of `ω₀|D`
-/


noncomputable section

namespace HryniewiczCriterion

variable {H : R4 → ℝ} {e : Plane → R4}

lemma smul_mem_openUnitDisk {v : Plane} (hv : v ∈ closedUnitDisk) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    t • v ∈ openUnitDisk := by
  simp only [closedUnitDisk, openUnitDisk, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
  have h0 := ht.1; have h1 := ht.2
  have : t ^ 2 < 1 := by nlinarith
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma smul_mem_openUnitDisk' {v : Plane} (hv : v ∈ openUnitDisk) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • v ∈ openUnitDisk := by
  simp only [openUnitDisk, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
  have h0 := ht.1; have h1 := ht.2
  have : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := by
  intro v hv; simp only [openUnitDisk, closedUnitDisk, mem_setOf_eq] at *; exact hv.le

lemma isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)) continuous_const

lemma zero_mem_openUnitDisk : (0 : Plane) ∈ openUnitDisk := by
  simp [openUnitDisk]

lemma eq_zero_at_one {g : ℝ → ℝ} (hg : Continuous g) (h : ∀ t ∈ Ico (0 : ℝ) 1, g t = 0) :
    g 1 = 0 := by
  have hc : IsClosed {t | g t = 0} := isClosed_eq hg continuous_const
  have hsub : closure (Ico (0 : ℝ) 1) ⊆ {t | g t = 0} := hc.closure_subset_iff.2 h
  rw [closure_Ico zero_ne_one] at hsub
  exact hsub ⟨zero_le_one, le_rfl⟩

lemma nonneg_at_one {g : ℝ → ℝ} (hg : Continuous g) (h : ∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ g t) :
    0 ≤ g 1 := by
  have hc : IsClosed {t | 0 ≤ g t} := isClosed_le continuous_const hg
  have hsub : closure (Ico (0 : ℝ) 1) ⊆ {t | 0 ≤ g t} := hc.closure_subset_iff.2 h
  rw [closure_Ico zero_ne_one] at hsub
  exact hsub ⟨zero_le_one, le_rfl⟩

variable (hH : ContDiff ℝ ∞ H) (he : ContDiff ℝ ∞ e)
  (hDS : ∀ v ∈ closedUnitDisk, H (e v) = 1)
include hH he hDS

lemma dH_fderiv_open {v : Plane} (hv : v ∈ openUnitDisk) (w : Plane) :
    fderiv ℝ H (e v) (fderiv ℝ e v w) = 0 := by
  have hev : (H ∘ e) =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_openUnitDisk.mem_nhds hv] with q hq
    exact hDS q (openUnitDisk_subset hq)
  have h0 : fderiv ℝ (H ∘ e) v = 0 := by rw [hev.fderiv_eq]; simp
  have hc : fderiv ℝ (H ∘ e) v = (fderiv ℝ H (e v)).comp (fderiv ℝ e v) :=
    fderiv_comp v ((hH.differentiable (by simp)) _) ((he.differentiable (by simp)) _)
  have := congrArg (fun L : Plane →L[ℝ] ℝ => L w) (hc.symm.trans h0)
  simpa using this

lemma contDiff_fderiv_e : ContDiff ℝ ∞ (fderiv ℝ e) := he.fderiv_right le_rfl

lemma dH_fderiv_closed {v : Plane} (hv : v ∈ closedUnitDisk) (w : Plane) :
    fderiv ℝ H (e v) (fderiv ℝ e v w) = 0 := by
  have hsm : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
  have hg : Continuous fun t : ℝ => fderiv ℝ H (e (t • v)) (fderiv ℝ e (t • v) w) :=
    ((contDiff_fderiv_of_smooth hH).continuous.comp (he.continuous.comp hsm)).clm_apply
      (((contDiff_fderiv_e hH he hDS).continuous.comp hsm).clm_apply continuous_const)
  have := eq_zero_at_one hg fun t ht =>
    dH_fderiv_open hH he hDS (smul_mem_openUnitDisk hv ht) w
  simpa using this

lemma dH_pos_closed (hS : IsStrictlyStarShapedLevel H) {v : Plane} (hv : v ∈ closedUnitDisk) :
    0 < fderiv ℝ H (e v) (e v) := hS.2.2 _ (hDS v hv)

omit hH he hDS in
lemma eq_smul_X_of_xiPsi_eq_zero {x w : R4} (hx : 0 < fderiv ℝ H x x) (hw : fderiv ℝ H x w = 0)
    (h0 : xiPsi H x w = 0) :
    w = (liouvilleForm x w / liouvilleForm x (hamiltonianVectorField H x)) •
      hamiltonianVectorField H x := by
  have h := reebProjection_eq_xiPsi hx hw
  rw [h0] at h
  simp only [Complex.zero_re, Complex.zero_im, zero_smul, add_zero] at h
  exact sub_eq_zero.1 h

lemma xiPsi_ne_zero_open (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) {w : Plane} (hw : w ≠ 0) :
    xiPsi H (e v) (fderiv ℝ e v w) ≠ 0 := by
  intro h0
  have hx := dH_pos_closed hH he hDS hS (openUnitDisk_subset hv)
  have h := eq_smul_X_of_xiPsi_eq_zero hx (dH_fderiv_open hH he hDS hv w) h0
  set c := liouvilleForm (e v) (fderiv ℝ e v w) /
    liouvilleForm (e v) (hamiltonianVectorField H (e v))
  by_cases hc : c = 0
  · rw [hc, zero_smul] at h
    exact hw (hinj v (openUnitDisk_subset hv) (by rw [h, map_zero]))
  · apply htr v hv
    refine ⟨c⁻¹ • w, ?_⟩
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- `ω₀` on the image of the standard basis. -/
def diskOmega (e : Plane → R4) (v : Plane) : ℝ :=
  omega0 (fderiv ℝ e v (Pi.single 0 1)) (fderiv ℝ e v (Pi.single 1 1))

omit hH he hDS in
lemma fderiv_plane_eq (v a : Plane) :
    fderiv ℝ e v a = a 0 • fderiv ℝ e v (Pi.single 0 1) + a 1 • fderiv ℝ e v (Pi.single 1 1) := by
  have ha : a = a 0 • (Pi.single 0 1 : Plane) + a 1 • (Pi.single 1 1 : Plane) := by
    ext i; fin_cases i <;> simp
  conv_lhs => rw [ha]
  simp only [map_add, map_smul]

omit hH he hDS in
lemma omega0_fderiv_plane (v a b : Plane) :
    omega0 (fderiv ℝ e v a) (fderiv ℝ e v b) = (a 0 * b 1 - a 1 * b 0) * diskOmega e v := by
  rw [fderiv_plane_eq v a, fderiv_plane_eq v b, diskOmega]
  simp only [omega0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma continuous_diskOmega : Continuous (diskOmega e) :=
  continuous_omega0 ((contDiff_fderiv_e hH he hDS).continuous.clm_apply continuous_const)
    ((contDiff_fderiv_e hH he hDS).continuous.clm_apply continuous_const)

lemma diskOmega_ne_zero (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) : diskOmega e v ≠ 0 := by
  intro hD
  have hx := dH_pos_closed hH he hDS hS (openUnitDisk_subset hv)
  set e0 : Plane := Pi.single 0 1
  set e1 : Plane := Pi.single 1 1
  set ζ := xiPsi H (e v) (fderiv ℝ e v e0)
  set η := xiPsi H (e v) (fderiv ℝ e v e1)
  have he0 : e0 ≠ 0 := fun h => by simpa [e0] using congrFun h 0
  have hζ : ζ ≠ 0 := xiPsi_ne_zero_open hH he hDS hS hinj htr hv he0
  have him : ((starRingEnd ℂ) ζ * η).im = 0 := by
    rw [xiPsi_im_conj_mul hx (dH_fderiv_open hH he hDS hv e0) (dH_fderiv_open hH he hDS hv e1)]
    exact hD
  set t : ℝ := (η / ζ).re
  have hηt : η = (t : ℂ) * ζ := by
    have him' : η.im * ζ.re - η.re * ζ.im = 0 := by
      simp [Complex.mul_im] at him; linarith
    have hreal : η / ζ = (t : ℂ) := by
      apply Complex.ext
      · simp [t]
      · rw [Complex.div_im, ← sub_div, him', zero_div]; simp
    rw [← hreal, div_mul_cancel₀ _ hζ]
  have hw : (1 : ℝ) • e1 + (-t) • e0 ≠ 0 := fun h => by
    have := congrFun h 1
    simp [e0, e1] at this
  apply xiPsi_ne_zero_open hH he hDS hS hinj htr hv hw
  rw [map_add, map_smul, map_smul, xiPsi_add_smul]
  change ((1 : ℝ) : ℂ) * η + ((-t : ℝ) : ℂ) * ζ = 0
  rw [hηt]; push_cast; ring

lemma diskOmega_mul_pos (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) : 0 < diskOmega e v * diskOmega e 0 := by
  have hD0 := diskOmega_ne_zero hH he hDS hS hinj htr zero_mem_openUnitDisk
  by_contra hle
  push_neg at hle
  set h : ℝ → ℝ := fun t => diskOmega e (t • v) * diskOmega e 0
  have hc : Continuous h :=
    ((continuous_diskOmega hH he hDS).comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h 0 = diskOmega e 0 * diskOmega e 0 := by simp [h]
  have h1 : h 1 = diskOmega e v * diskOmega e 0 := by simp [h]
  have hmem : (0 : ℝ) ∈ Icc (h 1) (h 0) := ⟨by rw [h1]; exact hle, by rw [h0]; exact mul_self_nonneg _⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' zero_le_one hc.continuousOn hmem
  have := diskOmega_ne_zero hH he hDS hS hinj htr (smul_mem_openUnitDisk' hv ht)
  exact this (by simpa [h, hD0] using hzero)

lemma diskOmega_mul_nonneg (hS : IsStrictlyStarShapedLevel H)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ closedUnitDisk) : 0 ≤ diskOmega e v * diskOmega e 0 := by
  have hc : Continuous fun t : ℝ => diskOmega e (t • v) * diskOmega e 0 :=
    ((continuous_diskOmega hH he hDS).comp (continuous_id.smul continuous_const)).mul continuous_const
  have := nonneg_at_one hc fun t ht =>
    (diskOmega_mul_pos hH he hDS hS hinj htr (smul_mem_openUnitDisk hv ht)).le
  simpa using this

end HryniewiczCriterion

/-!
# Steps for `disk_conormal_xi_winding_eq_one`
-/


noncomputable section

namespace HryniewiczCriterion

/-- The curve `u` on the unit circle: `|u|² = 1`, `⟨u, u'⟩ = 0`, and `u'` never vanishes
when `de(u) u' = T X ≠ 0`. The turning rate `κ = det(u, u')` therefore never vanishes. -/
lemma circle_kappa_ne_zero {u : ℝ → Plane} (hu : ContDiff ℝ ∞ u) (hucirc : ∀ s, u s ∈ unitCircle)
    (hu'ne : ∀ s, deriv u s ≠ 0) (s : ℝ) :
    u s 0 * deriv u s 1 - u s 1 * deriv u s 0 ≠ 0 := by
  have hd : ∀ t, HasDerivAt u (deriv u t) t := fun t => ((hu.differentiable (by simp)) t).hasDerivAt
  have hdi : ∀ t i, HasDerivAt (fun t => u t i) (deriv u t i) t := fun t i => hasDerivAt_pi.1 (hd t) i
  have hsq : HasDerivAt (fun t => u t 0 * u t 0 + u t 1 * u t 1)
      (deriv u s 0 * u s 0 + u s 0 * deriv u s 0 + (deriv u s 1 * u s 1 + u s 1 * deriv u s 1)) s :=
    ((hdi s 0).mul (hdi s 0)).add ((hdi s 1).mul (hdi s 1))
  have hconst : (fun t => u t 0 * u t 0 + u t 1 * u t 1) = fun _ => (1 : ℝ) := funext fun t => by
    have := hucirc t; simp only [unitCircle, mem_setOf_eq] at this; linarith
  rw [hconst] at hsq
  have hdot : u s 0 * deriv u s 0 + u s 1 * deriv u s 1 = 0 := by
    have := hsq.unique (hasDerivAt_const s 1); linarith
  have h1 : u s 0 ^ 2 + u s 1 ^ 2 = 1 := hucirc s
  intro hk
  have hid : (u s 0 * deriv u s 1 - u s 1 * deriv u s 0) ^ 2 +
      (u s 0 * deriv u s 0 + u s 1 * deriv u s 1) ^ 2 =
      (u s 0 ^ 2 + u s 1 ^ 2) * (deriv u s 0 ^ 2 + deriv u s 1 ^ 2) := by ring
  rw [hk, hdot, h1] at hid
  apply hu'ne s
  ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (deriv u s 0), sq_nonneg (deriv u s 1)]

/-- A continuous nowhere-vanishing real function on `ℝ` has constant sign. -/
lemma mul_pos_of_ne_zero_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (hne : ∀ s, f s ≠ 0)
    (s : ℝ) : 0 < f s * f 0 := by
  by_contra hle
  push_neg at hle
  set h : ℝ → ℝ := fun t => f t * f 0
  have hc : Continuous h := hf.mul continuous_const
  have hmem : (0 : ℝ) ∈ uIcc (h 0) (h s) :=
    Set.mem_uIcc.2 (Or.inr ⟨hle, mul_self_nonneg _⟩)
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hc.continuousOn hmem
  exact mul_ne_zero (hne t) (hne 0) ht

lemma div_im_eq (a b : ℂ) : (a / b).im = ((starRingEnd ℂ) b * a).im / Complex.normSq b := by
  rw [Complex.div_im, Complex.mul_im]; simp; ring

end HryniewiczCriterion

/-!
# `disk_conormal_xi_winding_eq_one`
-/


noncomputable section

namespace HryniewiczCriterion

theorem disk_conormal_xi_winding_eq_one' (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e)
    (hDS : e '' closedUnitDisk ⊆ energySurface H) (hbd : e '' unitCircle = P.image)
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    (u : ℝ → Plane) (hu : ContDiff ℝ ∞ u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (heu : ∀ s, e (u s) = P.x (P.T * s)) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧ (∀ s, r (s + 1) = r s) ∧
      (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (P.T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (P.T * s)) (hamiltonianVectorField H (P.x (P.T * s)))) • hamiltonianVectorField H (P.x (P.T * s))) =
        r s • (Real.cos (θ s) • xiFrame1 H (P.x (P.T * s)) + Real.sin (θ s) • xiFrame2 H (P.x (P.T * s))) := by
  have hH : ContDiff ℝ ∞ H := hS.1
  have hE : ContDiff ℝ ∞ e := he.1
  have hinj := he.2.2
  have hD : ∀ v ∈ closedUnitDisk, H (e v) = 1 := fun v hv => hDS ⟨v, hv, rfl⟩
  have hcl : ∀ s, u s ∈ closedUnitDisk := fun s => le_of_eq (hucirc s)
  have hpos : ∀ v ∈ closedUnitDisk, 0 < fderiv ℝ H (e v) (e v) := fun v hv =>
    dH_pos_closed hH hE hD hS hv
  set T := P.T
  have hT : 0 < T := P.T_pos
  have hd : ∀ t, HasDerivAt u (deriv u t) t := fun t => ((hu.differentiable (by simp)) t).hasDerivAt
  have hdc : Continuous (deriv u) := hu.continuous_deriv (by simp)
  have hu1 : u 1 = u 0 := by simpa using huper 0
  set X := hamiltonianVectorField H
  ------------------------------------------------------------------
  -- Step 1: `de(u) u' = T X`.
  have hdu : ∀ s, fderiv ℝ e (u s) (deriv u s) = T • X (e (u s)) := by
    intro s
    have h1 : HasDerivAt (fun s => e (u s)) (fderiv ℝ e (u s) (deriv u s)) s :=
      ((hE.differentiable (by simp)) (u s)).hasFDerivAt.comp_hasDerivAt s (hd s)
    have h2 : HasDerivAt (fun s => P.x (T * s)) ((T : ℝ) • X (P.x (T * s))) s := by
      have := (P.trajectory.1 (T * s)).scomp s ((hasDerivAt_id s).const_mul T)
      convert this using 1 <;> first | rfl | simp [X]
    have hfun : (fun s => e (u s)) = fun s => P.x (T * s) := funext heu
    rw [hfun] at h1
    rw [h1.unique h2, heu s]
  have hXne : ∀ s, X (e (u s)) ≠ 0 := by
    intro s h0
    have := omega0_y_X (H := H) (e (u s))
    rw [show hamiltonianVectorField H (e (u s)) = 0 from h0] at this
    have hp := hpos _ (hcl s)
    simp [omega0] at this
    linarith
  have hu'ne : ∀ s, deriv u s ≠ 0 := by
    intro s h0
    have := hdu s
    rw [h0, map_zero] at this
    exact hXne s (smul_eq_zero.1 this.symm |>.resolve_left hT.ne')
  set κ : ℝ → ℝ := fun s => u s 0 * deriv u s 1 - u s 1 * deriv u s 0
  have hκne : ∀ s, κ s ≠ 0 := circle_kappa_ne_zero hu hucirc hu'ne
  have hκc : Continuous κ := by
    have h0 := (continuous_apply 0).comp hu.continuous
    have h1 := (continuous_apply 1).comp hu.continuous
    have d0 := (continuous_apply 0).comp hdc
    have d1 := (continuous_apply 1).comp hdc
    exact (h0.mul d1).sub (h1.mul d0)
  have hκsign : ∀ s, 0 < κ s * κ 0 := mul_pos_of_ne_zero_of_continuous hκc hκne
  set D0 := diskOmega e 0
  have hD0 : D0 ≠ 0 := diskOmega_ne_zero hH hE hD hS hinj htr zero_mem_openUnitDisk
  ------------------------------------------------------------------
  -- Step 2: the action identity forces `κ · D₀ > 0`.
  have hsmulcl : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, r • u s ∈ closedUnitDisk := by
    intro r hr s
    have h1 : u s 0 ^ 2 + u s 1 ^ 2 = 1 := hucirc s
    simp only [closedUnitDisk, mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    have : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
    nlinarith
  have hκD : 0 < κ 0 * D0 := by
    by_contra hneg
    push_neg at hneg
    have hlt : κ 0 * D0 < 0 := lt_of_le_of_ne hneg (mul_ne_zero (hκne 0) hD0)
    set c : ℝ → ℝ → R4 := fun r s => e (r • u s) with hc
    have hcs : ContDiff ℝ ∞ (Function.uncurry c) :=
      hE.comp (contDiff_fst.smul (hu.comp contDiff_snd))
    have hper' : ∀ r, c r 1 = c r 0 := fun r => by simp [c, hu1]
    have h0' : ∀ s, c 0 s = c 0 0 := fun s => by simp [c]
    have hid := action_identity hcs hper' h0'
    have hpr : ∀ r s, fderiv ℝ (Function.uncurry c) (r, s) (1, 0) = fderiv ℝ e (r • u s) (u s) := by
      intro r s
      have hΦ := ((hcs.differentiable (by simp)) (r, s)).hasFDerivAt
      have h1 := HasFDerivAt.comp_hasDerivAt (l := Function.uncurry c)
        (f := fun r => ((r, s) : ℝ × ℝ)) r hΦ ((hasDerivAt_id r).prodMk (hasDerivAt_const r s))
      have h2 : HasDerivAt (fun r => e (r • u s)) (fderiv ℝ e (r • u s) (u s)) r := by
        have := ((hE.differentiable (by simp)) (r • u s)).hasFDerivAt.comp_hasDerivAt r
          ((hasDerivAt_id r).smul_const (u s))
        convert this using 1 <;> first | rfl | simp
      exact h1.unique h2
    have hps : ∀ r s, fderiv ℝ (Function.uncurry c) (r, s) (0, 1) =
        fderiv ℝ e (r • u s) (r • deriv u s) := by
      intro r s
      have hΦ := ((hcs.differentiable (by simp)) (r, s)).hasFDerivAt
      have h1 := HasFDerivAt.comp_hasDerivAt (l := Function.uncurry c)
        (f := fun s => ((r, s) : ℝ × ℝ)) s hΦ ((hasDerivAt_const s r).prodMk (hasDerivAt_id s))
      have h2 : HasDerivAt (fun s => e (r • u s)) (fderiv ℝ e (r • u s) (r • deriv u s)) s :=
        ((hE.differentiable (by simp)) (r • u s)).hasFDerivAt.comp_hasDerivAt s
          ((hd s).const_smul r)
      exact h1.unique h2
    have hL : 0 < ∫ s in (0 : ℝ)..1, omega0 (c 1 s) (fderiv ℝ (Function.uncurry c) (1, s) (0, 1)) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ zero_lt_one
      · exact (continuous_omega0 (hcs.continuous.comp (continuous_const.prodMk continuous_id))
          (((hcs.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_apply
            continuous_const)).intervalIntegrable 0 1
      · intro s _
        rw [hps]
        simp only [c, one_smul]
        rw [hdu s]
        have h1 : omega0 (e (u s)) (T • X (e (u s))) = T * omega0 (e (u s)) (X (e (u s))) := by
          simp [omega0]; ring
        rw [h1, omega0_y_X]
        exact mul_pos hT (hpos _ (hcl s))
    have hR : ∫ s in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        omega0 (fderiv ℝ (Function.uncurry c) (r, s) (1, 0))
          (fderiv ℝ (Function.uncurry c) (r, s) (0, 1)) ≤ 0 := by
      rw [← neg_nonneg, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_nonneg zero_le_one
      intro s _
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_nonneg zero_le_one
      intro r hr
      rw [hpr, hps, omega0_fderiv_plane]
      have hnn := diskOmega_mul_nonneg hH hE hD hS hinj htr (hsmulcl r hr s)
      set Dr := diskOmega e (r • u s)
      have key : κ s * Dr ≤ 0 := by
        by_contra hp
        push_neg at hp
        have e1 : (κ s * Dr) * (κ 0 * D0) = (κ s * κ 0) * (Dr * D0) := by ring
        have h1 : (κ s * Dr) * (κ 0 * D0) < 0 := mul_neg_of_pos_of_neg hp hlt
        have h2 : 0 ≤ (κ s * κ 0) * (Dr * D0) := mul_nonneg (hκsign s).le hnn
        linarith
      have e2 : (u s 0 * (r • deriv u s) 1 - u s 1 * (r • deriv u s) 0) * Dr = r * (κ s * Dr) := by
        simp only [κ, Pi.smul_apply, smul_eq_mul]; ring
      rw [e2]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hr.1 key]
    linarith
  have hκD' : ∀ s, 0 < κ s * D0 := by
    intro s
    have h1 := hκsign s
    have h2 : 0 < κ 0 * κ 0 := mul_self_pos.2 (hκne 0)
    have : 0 < (κ s * D0) * (κ 0 * κ 0) := by nlinarith
    exact pos_of_mul_pos_left this h2.le
  ------------------------------------------------------------------
  -- Step 3: the loop at the centre winds once.
  have hune : ∀ s, u s ≠ 0 := by
    intro s h0
    have h1 : u s 0 ^ 2 + u s 1 ^ 2 = 1 := hucirc s
    rw [h0] at h1; simp at h1
  have h0cl : (0 : Plane) ∈ closedUnitDisk := openUnitDisk_subset zero_mem_openUnitDisk
  set ζ := xiPsi H (e 0) (fderiv ℝ e 0 (Pi.single 0 1))
  set η := xiPsi H (e 0) (fderiv ℝ e 0 (Pi.single 1 1))
  have hlin : ∀ w : Plane, xiPsi H (e 0) (fderiv ℝ e 0 w) = (w 0 : ℂ) * ζ + (w 1 : ℂ) * η := by
    intro w; rw [fderiv_plane_eq 0 w, xiPsi_add_smul]
  set c0 : ℝ → ℂ := fun s => xiPsi H (e 0) (fderiv ℝ e 0 (u s)) with hc0
  set c0' : ℝ → ℂ := fun s => xiPsi H (e 0) (fderiv ℝ e 0 (deriv u s)) with hc0'
  have hc0d : ∀ s, HasDerivAt c0 (c0' s) s := by
    intro s
    have h0 := (hasDerivAt_pi.1 (hd s) 0).ofReal_comp
    have h1 := (hasDerivAt_pi.1 (hd s) 1).ofReal_comp
    have h := (h0.mul_const ζ).add (h1.mul_const η)
    have e1 : c0 = fun s => ((u s 0 : ℝ) : ℂ) * ζ + ((u s 1 : ℝ) : ℂ) * η := funext fun s => hlin _
    rw [e1]
    show HasDerivAt _ (xiPsi H (e 0) (fderiv ℝ e 0 (deriv u s))) s
    rw [hlin]; exact h
  have hc0'c : Continuous c0' := by
    have e1 : c0' = fun s => ((deriv u s 0 : ℝ) : ℂ) * ζ + ((deriv u s 1 : ℝ) : ℂ) * η :=
      funext fun s => hlin _
    rw [e1]
    exact ((continuous_ofReal.comp ((continuous_apply 0).comp hdc)).mul continuous_const).add
      ((continuous_ofReal.comp ((continuous_apply 1).comp hdc)).mul continuous_const)
  have hc0ne : ∀ s, c0 s ≠ 0 := fun s =>
    xiPsi_ne_zero_open hH hE hD hS hinj htr zero_mem_openUnitDisk (hune s)
  have hc0per : c0 1 = c0 0 := by simp only [c0, hu1]
  have hc0pos : ∀ t, 0 < (c0' t / c0 t).im := by
    intro t
    rw [div_im_eq, xiPsi_im_conj_mul (hpos 0 h0cl)
      (dH_fderiv_open hH hE hD zero_mem_openUnitDisk _) (dH_fderiv_open hH hE hD zero_mem_openUnitDisk _),
      omega0_fderiv_plane]
    exact div_pos (hκD' t) (Complex.normSq_pos.2 (hc0ne t))
  have hray : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ l : ℝ, 0 < l → c0 t ≠ (l : ℂ) * c0 0 := by
    intro t ht l hl heq
    have hw : (1 : ℝ) • u t + (-l) • u 0 = 0 := by
      by_contra hw
      apply xiPsi_ne_zero_open hH hE hD hS hinj htr zero_mem_openUnitDisk hw
      rw [map_add, map_smul, map_smul, xiPsi_add_smul]
      change ((1 : ℝ) : ℂ) * c0 t + ((-l : ℝ) : ℂ) * c0 0 = 0
      rw [heq]; push_cast; ring
    have hut : u t = l • u 0 := by
      rw [one_smul, neg_smul, ← sub_eq_add_neg, sub_eq_zero] at hw; exact hw
    have h1 : u t 0 ^ 2 + u t 1 ^ 2 = 1 := hucirc t
    have h2 : u 0 0 ^ 2 + u 0 1 ^ 2 = 1 := hucirc 0
    rw [hut] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have hl1 : l = 1 := by
      have : l ^ 2 = 1 := by nlinarith
      nlinarith
    rw [hl1, one_smul] at hut
    apply hP (T * t) (mul_pos hT ht.1) (by nlinarith [ht.2])
    rw [← heu t, hut, heu 0, mul_zero]
  have hW0 := WindA.integral_eq_two_pi_I_of_im_pos hc0d hc0'c hc0ne hc0per hc0pos hray
  ------------------------------------------------------------------
  -- Step 4: boundary non-vanishing and homotopy to the boundary loop.
  have hbne : ∀ s, xiPsi H (e (u s)) (fderiv ℝ e (u s) (u s)) ≠ 0 := by
    intro s h0
    have htan := dH_fderiv_closed hH hE hD (hcl s) (u s)
    have hν := eq_smul_X_of_xiPsi_eq_zero (hpos _ (hcl s)) htan h0
    set k := liouvilleForm (e (u s)) (fderiv ℝ e (u s) (u s)) /
      liouvilleForm (e (u s)) (hamiltonianVectorField H (e (u s)))
    have hz : fderiv ℝ e (u s) (u s - (k / T) • deriv u s) = fderiv ℝ e (u s) 0 := by
      rw [map_sub, map_smul, hdu s, smul_smul, div_mul_cancel₀ _ hT.ne', map_zero, sub_eq_zero]
      exact hν
    have hus : u s = (k / T) • deriv u s := sub_eq_zero.1 (hinj _ (hcl s) hz)
    apply hκne s
    simp only [κ]
    rw [hus]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  set Ψ : Plane × Plane → ℂ := fun q => xiPsi H (e q.1) (fderiv ℝ e q.1 q.2) with hΨdef
  have hΨ : ∀ q : Plane × Plane, q.1 ∈ closedUnitDisk → ContDiffAt ℝ ∞ Ψ q := by
    intro q hq
    have hg : ContDiff ℝ ∞ (fun q : Plane × Plane => (e q.1, fderiv ℝ e q.1 q.2)) :=
      (hE.comp contDiff_fst).prodMk
        (((contDiff_fderiv_e hH hE hD).comp contDiff_fst).clm_apply contDiff_snd)
    exact ContDiffAt.comp (g := fun p : R4 × R4 => xiPsi H p.1 p.2) q
      (contDiffAt_xiPsi hH (hpos _ hq)) hg.contDiffAt
  set F : ℝ → ℝ → ℂ := fun r s => Ψ (r • u s, u s) with hFdef
  have hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 • u p.2, u p.2)) :=
    (contDiff_fst.smul (hu.comp contDiff_snd)).prodMk (hu.comp contDiff_snd)
  have hFs : ∀ p : ℝ × ℝ, p.1 ∈ Icc (0 : ℝ) 1 → ContDiffAt ℝ ∞ (Function.uncurry F) p := by
    intro p hp
    exact ContDiffAt.comp (g := Ψ) p (hΨ _ (hsmulcl p.1 hp p.2)) hG.contDiffAt
  set F' : ℝ → ℝ → ℂ := fun r s => fderiv ℝ (Function.uncurry F) (r, s) (0, 1) with hF'def
  have hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, HasDerivAt (F r) (F' r s) s := by
    intro r hr s
    exact HasFDerivAt.comp_hasDerivAt (l := Function.uncurry F) (f := fun s => ((r, s) : ℝ × ℝ)) s
      ((hFs (r, s) hr).differentiableAt (by simp)).hasFDerivAt
      ((hasDerivAt_const s r).prodMk (hasDerivAt_id s))
  have hcF : ContinuousOn (Function.uncurry F) (Icc 0 1 ×ˢ univ) := fun p hp =>
    (hFs p hp.1).continuousAt.continuousWithinAt
  have hcF' : ContinuousOn (Function.uncurry F') (Icc 0 1 ×ˢ univ) := by
    intro p hp
    have h := ((hFs p hp.1).fderiv_right (m := ∞) le_rfl).continuousAt.clm_apply
      (continuousAt_const (y := ((0 : ℝ), (1 : ℝ))))
    exact h.continuousWithinAt
  have hFne : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s, F r s ≠ 0 := by
    intro r hr s
    rcases lt_or_eq_of_le hr.2 with h | h
    · exact xiPsi_ne_zero_open hH hE hD hS hinj htr (smul_mem_openUnitDisk (hcl s) ⟨hr.1, h⟩)
        (hune s)
    · simp only [F, Ψ, h, one_smul]; exact hbne s
  have hFper : ∀ r ∈ Icc (0 : ℝ) 1, F r 1 = F r 0 := fun r _ => by simp only [F, hu1]
  have hhom := WindA.integral_eq_of_homotopy hF hcF hcF' hFne hFper
  have hF0 : F 0 = c0 := funext fun s => by simp [F, Ψ, c0]
  have hF'0 : ∀ s, F' 0 s = c0' s := by
    intro s
    have := hF 0 ⟨le_rfl, zero_le_one⟩ s
    rw [hF0] at this
    exact this.unique (hc0d s)
  set cfin : ℝ → ℂ := fun s => xiPsi H (e (u s)) (fderiv ℝ e (u s) (u s)) with hcfin
  have hF1 : F 1 = cfin := funext fun s => by simp [F, Ψ, cfin]
  have hF'1 : ∀ s, F' 1 s = deriv cfin s := by
    intro s
    have := hF 1 ⟨zero_le_one, le_rfl⟩ s
    rw [hF1] at this
    exact this.deriv.symm
  have hW1 : ∫ s in (0 : ℝ)..1, deriv cfin s / cfin s = 2 * Real.pi * I := by
    have e1 : (∫ s in (0 : ℝ)..1, deriv cfin s / cfin s) = ∫ s in (0 : ℝ)..1, F' 1 s / F 1 s := by
      simp only [hF'1, hF1]
    have e0 : (∫ s in (0 : ℝ)..1, F' 0 s / F 0 s) = ∫ s in (0 : ℝ)..1, c0' s / c0 s := by
      simp only [hF'0, hF0]
    rw [e1, hhom, e0, hW0]
  ------------------------------------------------------------------
  -- Step 5: smooth polar form of the boundary loop.
  have hcfs : ContDiff ℝ ∞ cfin := by
    rw [contDiff_iff_contDiffAt]
    intro s
    exact ContDiffAt.comp (g := Ψ) s (hΨ _ (hcl s)) (hu.prodMk hu).contDiffAt
  have hcper : ∀ s, cfin (s + 1) = cfin s := fun s => by simp only [cfin, huper]
  obtain ⟨r, θ, hr, hθ, hrpos, hrper, hθper, hpolar⟩ :=
    WindA.exists_polar_of_winding_one hcfs hbne hcper hW1
  refine ⟨r, θ, hr, hθ, hrpos, hrper, hθper, fun s => ?_⟩
  ------------------------------------------------------------------
  -- Step 6: the identity in `ξ`.
  rw [← heu s]
  have hx := hpos _ (hcl s)
  have htan := dH_fderiv_closed hH hE hD (hcl s) (u s)
  have hrep := reebProjection_eq_xiPsi hx htan
  change reebProjection H (e (u s)) (fderiv ℝ e (u s) (u s)) = _
  have hp : xiPsi H (e (u s)) (fderiv ℝ e (u s) (u s)) =
      (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I) := hpolar s
  rw [hrep, hp]
  have hre : ((r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I)).re = r s * Real.cos (θ s) := by
    simp [Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have him : ((r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * I)).im = r s * Real.sin (θ s) := by
    simp [Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  rw [hre, him, smul_add, smul_smul, smul_smul]

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    (e : Plane → R4) (he : IsSmoothDiskEmbedding e)
    (hDS : e '' closedUnitDisk ⊆ energySurface H) (hbd : e '' unitCircle = P.image)
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    (u : ℝ → Plane) (hu : ContDiff ℝ ∞ u) (huper : ∀ s, u (s + 1) = u s)
    (hucirc : ∀ s, u s ∈ unitCircle) (heu : ∀ s, e (u s) = P.x (P.T * s)) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧ (∀ s, r (s + 1) = r s) ∧
      (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, (fderiv ℝ e (u s) (u s) - (liouvilleForm (P.x (P.T * s)) (fderiv ℝ e (u s) (u s)) / liouvilleForm (P.x (P.T * s)) (hamiltonianVectorField H (P.x (P.T * s)))) • hamiltonianVectorField H (P.x (P.T * s))) =
        r s • (Real.cos (θ s) • xiFrame1 H (P.x (P.T * s)) + Real.sin (θ s) • xiFrame2 H (P.x (P.T * s))) :=
  disk_conormal_xi_winding_eq_one' H hS P hP e he hDS hbd htr u hu huper hucirc heu
