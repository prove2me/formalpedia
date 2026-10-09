-- Prove2me | solution 1 for HryniewiczCriterion.linksNontrivially_of_isDiskLikeGlobalSectionMap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-08T18:16:22.498498+00:00
-- url     : https://prove2.me/submissions/3ee83e89-66f4-480d-9016-2ddb1367afbd

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorems.Thm_HryniewiczCriterion_isLinkingNumber_of_gaussLinkingIntegral_eq
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_twisted_pushOff
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_ne_zero_of_transverse_disk
import Theorems.Thm_HryniewiczCriterion_exists_prime_periodicOrbit_cover
import Theorems.Thm_HryniewiczCriterion_gaussLinkingIntegral_comp_mul_nat
import Theorems.Thm_HryniewiczCriterion_exists_circle_param_of_image_eq

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Topology

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
# Reduction of the twisting formula `sl(P) = m - k` to two Gauss-integral lemmas
-/


noncomputable section

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Euclidean norm and radial normalization -/

lemma slt_euclidNorm_smul (c : ℝ) (v : R4) : euclidNorm (c • v) = |c| * euclidNorm v := by
  have h : dot4 (c • v) (c • v) = c ^ 2 * dot4 v v := by
    simp [dot4, Fin.sum_univ_four]; ring
  rw [euclidNorm, euclidNorm, h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma slt_euclidNorm_pos {v : R4} (hv : v ≠ 0) : 0 < euclidNorm v :=
  Real.sqrt_pos.2 (dot4_pos hv)

lemma slt_radialNormalize_smul {c : ℝ} (hc : 0 < c) (v : R4) :
    radialNormalize (c • v) = radialNormalize v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [radialNormalize]
  rw [radialNormalize, radialNormalize, slt_euclidNorm_smul, abs_of_pos hc, smul_smul]
  congr 1
  have := (slt_euclidNorm_pos hv).ne'
  field_simp

lemma slt_euclidNorm_radialNormalize {v : R4} (hv : v ≠ 0) :
    euclidNorm (radialNormalize v) = 1 := by
  have hp := slt_euclidNorm_pos hv
  rw [radialNormalize, slt_euclidNorm_smul, abs_of_pos (inv_pos.2 hp), inv_mul_cancel₀ hp.ne']

lemma slt_contDiff_euclidNorm {v : ℝ → R4} (hv : ContDiff ℝ ∞ v) (hne : ∀ s, v s ≠ 0) :
    ContDiff ℝ ∞ (fun s => euclidNorm (v s)) := by
  have hdot : ContDiff ℝ ∞ (fun s => dot4 (v s) (v s)) := by
    have h := fun i => contDiff_pi.1 hv i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  exact hdot.sqrt fun s => (dot4_pos (hne s)).ne'

lemma slt_contDiff_radialNormalize {v : ℝ → R4} (hv : ContDiff ℝ ∞ v) (hne : ∀ s, v s ≠ 0) :
    ContDiff ℝ ∞ (fun s => radialNormalize (v s)) :=
  ((slt_contDiff_euclidNorm hv hne).inv fun s => (slt_euclidNorm_pos (hne s)).ne').smul hv

/-! ### Primeness: the loop `s ↦ x(Ts)` is injective modulo `1` -/

lemma slt_orbit_shift (hH : ContDiff ℝ ∞ H) (P : PeriodicOrbit H) {a b : ℝ}
    (hab : P.x a = P.x b) (t : ℝ) : P.x (t + (b - a)) = P.x t := by
  have hper : Function.Periodic P.x P.T := P.periodic
  have hxc : Continuous P.x := (trajectory_contDiff hH P.trajectory).continuous
  obtain ⟨R, hR⟩ := (hper.compact_of_continuous P.T_pos.ne' hxc).isBounded.subset_closedBall 0
  have hX : ContDiff ℝ ∞ (hamiltonianVectorField H) := contDiff_hvf hH
  obtain ⟨K, hK⟩ := (hX.contDiffOn (s := Metric.closedBall (0 : R4) R)).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hf : ∀ t, HasDerivAt (fun t => P.x (t + (b - a)))
      (hamiltonianVectorField H (P.x (t + (b - a)))) t ∧
      P.x (t + (b - a)) ∈ Metric.closedBall (0 : R4) R := fun t =>
    ⟨(P.trajectory.1 _).comp_add_const t (b - a), hR (Set.mem_range_self _)⟩
  have hg : ∀ t, HasDerivAt P.x (hamiltonianVectorField H (P.x t)) t ∧
      P.x t ∈ Metric.closedBall (0 : R4) R := fun t =>
    ⟨P.trajectory.1 t, hR (Set.mem_range_self _)⟩
  have := ODE_solution_unique_univ (v := fun _ => hamiltonianVectorField H)
    (s := fun _ => Metric.closedBall (0 : R4) R) (t₀ := a) (fun _ => hK) hf hg
    (by simp [hab])
  exact congrFun this t

lemma slt_orbit_eq_period (hH : ContDiff ℝ ∞ H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    {a b : ℝ} (hab : P.x a = P.x b) : ∃ n : ℤ, b - a = n * P.T := by
  have hper : Function.Periodic P.x P.T := P.periodic
  set d := b - a
  set n := ⌊d / P.T⌋
  have hT := P.T_pos
  have h1 : (n : ℝ) * P.T ≤ d := by
    have := Int.floor_le (d / P.T); rwa [le_div_iff₀ hT] at this
  have h2 : d < (n + 1) * P.T := by
    have := Int.lt_floor_add_one (d / P.T); rwa [div_lt_iff₀ hT] at this
  have hr : P.x (d - n * P.T) = P.x 0 := by
    rw [hper.sub_int_mul_eq n]
    have := slt_orbit_shift hH P hab 0
    simpa [d] using this
  refine ⟨n, ?_⟩
  by_contra hne
  have hpos : 0 < d - n * P.T := lt_of_le_of_ne (by linarith) (fun h => hne (by linarith))
  exact hP _ hpos (by linarith) hr

/-! ### The frame determinant -/

lemma slt_det4 (u v w z : R4) :
    Matrix.det (Matrix.of ![u, v, w, z]) =
      u 0 * (v 1 * (w 2 * z 3 - w 3 * z 2) - v 2 * (w 1 * z 3 - w 3 * z 1) + v 3 * (w 1 * z 2 - w 2 * z 1))
      - u 1 * (v 0 * (w 2 * z 3 - w 3 * z 2) - v 2 * (w 0 * z 3 - w 3 * z 0) + v 3 * (w 0 * z 2 - w 2 * z 0))
      + u 2 * (v 0 * (w 1 * z 3 - w 3 * z 1) - v 1 * (w 0 * z 3 - w 3 * z 0) + v 3 * (w 0 * z 1 - w 1 * z 0))
      - u 3 * (v 0 * (w 1 * z 2 - w 2 * z 1) - v 1 * (w 0 * z 2 - w 2 * z 0) + v 2 * (w 0 * z 1 - w 1 * z 0)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  ring
lemma slt_det_frame (y g : R4) (n a b m c₁ c₂ : ℝ) :
    Matrix.det (Matrix.of ![n • y, a • y + b • ![-g 1, g 0, -g 3, g 2],
      m • (quatQ2 y - c₁ • y), m • (quatQ1 y - c₂ • y)]) =
      n * b * m ^ 2 * dot4 y y * (y 0 * g 0 + y 1 * g 1 + y 2 * g 2 + y 3 * g 3) := by
  rw [slt_det4]
  simp only [quatQ1, quatQ2, dot4, Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-! ### The reduction -/

theorem selfLinking_eq_sub_of_pushOff_winding' (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (P : PeriodicOrbit H) (hP : P.IsPrime)
    (r θ : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (hθ : ContDiff ℝ ∞ θ) (hr0 : ∀ s, 0 < r s)
    (hrper : ∀ s, r (s + 1) = r s) (k : ℤ) (hθper : ∀ s, θ (s + 1) = θ s + 2 * Real.pi * k)
    (m : ℤ)
    (hlink : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsLinkingNumber (orbitLoop P)
        (fun s => radialNormalize (P.x (P.T * s) + ε • (r s • (Real.cos (θ s) •
          xiFrame1 H (P.x (P.T * s)) + Real.sin (θ s) • xiFrame2 H (P.x (P.T * s)))))) m) :
    HasSelfLinkingNumber H P (m - k) := by
  have hH := hS.1
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by first | decide | simp | norm_num | exact_mod_cast le_top
  set y : ℝ → R4 := fun s => P.x (P.T * s) with hy_def
  have hy : ContDiff ℝ ∞ y := (trajectory_contDiff hH P.trajectory).comp
    (contDiff_const.mul contDiff_id)
  have hyS : ∀ s, H (y s) = 1 := fun s => P.trajectory.2 _
  have hpos : ∀ s, 0 < fderiv ℝ H (y s) (y s) := fun s => hS.2.2 _ (hyS s)
  have hy0 : ∀ s, y s ≠ 0 := fun s => ne_zero_of_dH_pos (hpos s)
  have hyper : ∀ s, y (s + 1) = y s := fun s => by
    simp only [hy_def, mul_add, mul_one]; exact P.periodic _
  set nr : ℝ → ℝ := fun s => euclidNorm (y s) with hnr_def
  have hnr : ContDiff ℝ ∞ nr := slt_contDiff_euclidNorm hy hy0
  have hnr0 : ∀ s, 0 < nr s := fun s => slt_euclidNorm_pos (hy0 s)
  set γ : ℝ → R4 := fun s => (nr s)⁻¹ • y s with hγ_def
  set e₁ : ℝ → R4 := fun s => (nr s)⁻¹ • xiFrame1 H (y s) with he₁_def
  set e₂ : ℝ → R4 := fun s => (nr s)⁻¹ • xiFrame2 H (y s) with he₂_def
  have hγ : ContDiff ℝ ∞ γ := (hnr.inv fun s => (hnr0 s).ne').smul hy
  have hZ₁ : ContDiff ℝ ∞ (fun s => xiFrame1 H (y s)) :=
    cd_xiFrame hH hy hpos quatQ2 (cd_quatQ2 hy)
  have hZ₂ : ContDiff ℝ ∞ (fun s => xiFrame2 H (y s)) :=
    cd_xiFrame hH hy hpos quatQ1 (cd_quatQ1 hy)
  have he₁ : ContDiff ℝ ∞ e₁ := (hnr.inv fun s => (hnr0 s).ne').smul hZ₁
  have he₂ : ContDiff ℝ ∞ e₂ := (hnr.inv fun s => (hnr0 s).ne').smul hZ₂
  have horbit : orbitLoop P = γ := rfl
  have hγunit : ∀ s, euclidNorm (γ s) = 1 := fun s => slt_euclidNorm_radialNormalize (hy0 s)
  -- injectivity modulo `1`
  have hinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n := by
    intro s t hst
    have hc : y t = (nr t / nr s) • y s := by
      have h' : y t = nr t • γ t := by
        simp only [hγ_def, smul_smul, mul_inv_cancel₀ (hnr0 t).ne', one_smul]
      rw [h', ← hst, hγ_def]; simp only [smul_smul]; ring_nf
    have hc0 : 0 < nr t / nr s := div_pos (hnr0 t) (hnr0 s)
    obtain ⟨ρ, _, huniq⟩ := hS.2.1 (y s) (hy0 s)
    have e1 : (1 : ℝ) = ρ := huniq 1 ⟨one_pos, by simpa using hyS s⟩
    have e2 : nr t / nr s = ρ := huniq _ ⟨hc0, by rw [← hc]; exact hyS t⟩
    have hyy : P.x (P.T * s) = P.x (P.T * t) := by
      have : y t = y s := by rw [hc, e2, ← e1, one_smul]
      exact this.symm
    obtain ⟨n, hn⟩ := slt_orbit_eq_period hH P hP hyy
    refine ⟨n, ?_⟩
    have hT := P.T_pos.ne'
    have : P.T * (t - s) = P.T * n := by linarith
    have := mul_left_cancel₀ hT this
    linarith
  -- orientation of the frame
  have hdet : ∀ s, 0 < Matrix.det (Matrix.of ![γ s, deriv γ s, e₁ s, e₂ s]) := by
    intro s
    have hyd : HasDerivAt y (P.T • hamiltonianVectorField H (y s)) s := by
      have := (P.trajectory.1 (P.T * s)).scomp s ((hasDerivAt_id s).const_mul P.T)
      rw [mul_one] at this
      exact this
    have hnd : HasDerivAt (fun s => (nr s)⁻¹) (deriv (fun s => (nr s)⁻¹) s) s :=
      (((hnr.inv fun s => (hnr0 s).ne').differentiable (by simp)) s).hasDerivAt
    have hγd : deriv γ s = deriv (fun s => (nr s)⁻¹) s • y s +
        ((nr s)⁻¹ * P.T) • hamiltonianVectorField H (y s) := by
      show deriv (fun s => (nr s)⁻¹ • y s) s = _
      rw [show deriv (fun s => (nr s)⁻¹ • y s) s = _ from (hnd.smul hyd).deriv, smul_smul, add_comm]
    set g : R4 := fun i => partialDeriv H (y s) i
    have hX : hamiltonianVectorField H (y s) = ![-g 1, g 0, -g 3, g 2] := rfl
    have hdH : fderiv ℝ H (y s) (y s) = y s 0 * g 0 + y s 1 * g 1 + y s 2 * g 2 + y s 3 * g 3 :=
      clm_apply_eq_sum _ _
    have he₁' : e₁ s = ((nr s)⁻¹ * (nr s)⁻¹) •
        (quatQ2 (y s) - (fderiv ℝ H (y s) (quatQ2 (y s)) / fderiv ℝ H (y s) (y s)) • y s) := by
      simp only [he₁_def, xiFrame1, xiFrameRaw, smul_smul]; rfl
    have he₂' : e₂ s = ((nr s)⁻¹ * (nr s)⁻¹) •
        (quatQ1 (y s) - (fderiv ℝ H (y s) (quatQ1 (y s)) / fderiv ℝ H (y s) (y s)) • y s) := by
      simp only [he₂_def, xiFrame2, xiFrameRaw, smul_smul]; rfl
    rw [hγd, he₁', he₂', hX, show γ s = (nr s)⁻¹ • y s from rfl, slt_det_frame, ← hdH]
    have hn := inv_pos.2 (hnr0 s)
    have := hpos s
    have := dot4_pos (hy0 s)
    have := P.T_pos
    positivity
  obtain ⟨N, hN, ε₁, hε₁, hC⟩ := gaussLinkingIntegral_twisted_pushOff γ e₁ e₂
    (hγ.of_le h2) (he₁.of_le h2)
    (he₂.of_le h2) (fun s => by simp only [hγ_def, hnr_def, hyper])
    (fun s => by simp only [he₁_def, hnr_def, hyper]) (fun s => by simp only [he₂_def, hnr_def, hyper])
    hγunit hinj hdet r θ (hr.of_le h2)
    (hθ.of_le h2) hr0 hrper k hθper
  obtain ⟨ε₀, hε₀, hlink⟩ := hlink
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun ε hε hεlt => ?_⟩
  obtain ⟨hne, hdisj, hNav, hG⟩ := hC ε hε (lt_of_lt_of_le hεlt (min_le_right _ _))
  -- rescaling: the child's push-offs are the platform push-offs
  have hB₀ : pushOffLoop H P ε = fun s => radialNormalize (γ s + ε • e₁ s) := by
    funext s
    have : γ s + ε • e₁ s = (nr s)⁻¹ • (y s + ε • xiFrame1 H (y s)) := by
      simp only [hγ_def, he₁_def, smul_add, smul_comm ε]
    rw [this, slt_radialNormalize_smul (inv_pos.2 (hnr0 s))]; rfl
  have hBV : (fun s => radialNormalize (P.x (P.T * s) + ε • (r s • (Real.cos (θ s) •
          xiFrame1 H (P.x (P.T * s)) + Real.sin (θ s) • xiFrame2 H (P.x (P.T * s)))))) =
      fun s => radialNormalize (γ s + ε • (r s • (Real.cos (θ s) • e₁ s +
        Real.sin (θ s) • e₂ s))) := by
    funext s
    have : γ s + ε • (r s • (Real.cos (θ s) • e₁ s + Real.sin (θ s) • e₂ s)) =
        (nr s)⁻¹ • (y s + ε • (r s • (Real.cos (θ s) • xiFrame1 H (y s) +
          Real.sin (θ s) • xiFrame2 H (y s)))) := by
      simp only [hγ_def, he₁_def, he₂_def]
      module
    rw [this, slt_radialNormalize_smul (inv_pos.2 (hnr0 s))]
  have hL := (hlink ε hε (lt_of_lt_of_le hεlt (min_le_left _ _))).2 N hN
    (fun s => by rw [hBV]; exact ⟨(hNav s).1, (hNav s).2.2⟩)
  rw [hBV, horbit, hG] at hL
  rw [hB₀, horbit]
  have hB₀cd : ContDiff ℝ ∞ (fun s => radialNormalize (γ s + ε • e₁ s)) :=
    slt_contDiff_radialNormalize (hγ.add (he₁.const_smul ε)) hne
  refine isLinkingNumber_of_gaussLinkingIntegral_eq γ _
    (hγ.of_le h2) (hB₀cd.of_le h2)
    (fun s => by simp only [hγ_def, hnr_def, hyper])
    (fun s => by simp only [hγ_def, he₁_def, hnr_def, hyper]) hγunit
    (fun s => slt_euclidNorm_radialNormalize (hne s)) hdisj N hN
    (fun s => ⟨(hNav s).1, (hNav s).2.1⟩) (m - k) ?_
  push_cast
  linarith

end HryniewiczCriterion

/-!
# Glue for `linksNontrivially_of_isDiskLikeGlobalSectionMap`, part 1

Radial normalization, disjointness of distinct orbits, and the transversality determinant
`det(e, X_H(e), ∂₀e, ∂₁e)` on a disk-like global section.
-/


noncomputable section

namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Radial normalization -/

lemma lk_eq_of_normalize_eq (hS : IsStrictlyStarShapedLevel H) {a b : R4} (ha : H a = 1)
    (hb : H b = 1) (h : radialNormalize a = radialNormalize b) : a = b := by
  have ha0 : a ≠ 0 := ne_zero_of_dH_pos (hS.2.2 a ha)
  have hb0 : b ≠ 0 := ne_zero_of_dH_pos (hS.2.2 b hb)
  have hna := slt_euclidNorm_pos ha0
  have hnb := slt_euclidNorm_pos hb0
  set c := euclidNorm a * (euclidNorm b)⁻¹ with hc
  have hcpos : 0 < c := mul_pos hna (inv_pos.2 hnb)
  have hab : a = c • b := by
    have h' := congrArg (fun y => euclidNorm a • y) h
    simp only [radialNormalize, smul_smul, mul_inv_cancel₀ hna.ne', one_smul] at h'
    rw [h', hc]
  obtain ⟨r, -, hr⟩ := hS.2.1 b hb0
  have h1 : (1 : ℝ) = r := hr 1 ⟨one_pos, by simpa using hb⟩
  have h2 : c = r := hr c ⟨hcpos, by rw [← hab]; exact ha⟩
  rw [hab, h2, ← h1, one_smul]

lemma lk_hasDerivAt_dot4 {a b : ℝ → R4} {a' b' : R4} {x : ℝ} (ha' : HasDerivAt a a' x)
    (hb' : HasDerivAt b b' x) :
    HasDerivAt (fun x => dot4 (a x) (b x)) (dot4 a' (b x) + dot4 (a x) b') x := by
  have ha : ∀ i, HasDerivAt (fun x => a x i) (a' i) x := fun i => (hasDerivAt_pi.1 ha') i
  have hb : ∀ i, HasDerivAt (fun x => b x i) (b' i) x := fun i => (hasDerivAt_pi.1 hb') i
  have h := ((((ha 0).mul (hb 0)).add ((ha 1).mul (hb 1))).add ((ha 2).mul (hb 2))).add
    ((ha 3).mul (hb 3))
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h
    (Filter.Eventually.of_forall fun y => ?_)) ?_
  · simp only [dot4, Fin.sum_univ_four, Pi.add_apply, Pi.mul_apply]
  · simp only [dot4, Fin.sum_univ_four]; ring

/-- Derivative of `t ↦ f(t)/|f(t)|`. -/
lemma lk_hasDerivAt_normalize {f : ℝ → R4} {f' : R4} {t : ℝ} (hf : HasDerivAt f f' t)
    (hne : f t ≠ 0) :
    HasDerivAt (fun t => radialNormalize (f t))
      ((euclidNorm (f t))⁻¹ • f' - (dot4 (f t) f' / euclidNorm (f t) ^ 3) • f t) t := by
  have hpos := slt_euclidNorm_pos hne
  have hq := lk_hasDerivAt_dot4 hf hf
  have hn : HasDerivAt (fun t => euclidNorm (f t)) (dot4 (f t) f' / euclidNorm (f t)) t := by
    have h := hq.sqrt (dot4_pos hne).ne'
    have hs : dot4 f' (f t) = dot4 (f t) f' := by simp only [dot4, Fin.sum_univ_four]; ring
    refine HasDerivAt.congr_deriv (f := fun x => euclidNorm (f x)) h ?_
    rw [hs]
    have h2 : Real.sqrt (dot4 (f t) (f t)) = euclidNorm (f t) := rfl
    rw [h2]
    field_simp
    ring
  have hinv := hn.inv hpos.ne'
  have h := hinv.smul hf
  refine h.congr_deriv ?_
  have hp := hpos.ne'
  simp only [Pi.inv_apply]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 1
  field_simp

lemma lk_contDiffAt_normalize {x : R4} (hx : x ≠ 0) : ContDiffAt ℝ ∞ radialNormalize x := by
  have hd : ContDiff ℝ ∞ (fun y : R4 => dot4 y y) := by
    have hid : ContDiff ℝ ∞ (fun y : R4 => y) := contDiff_id
    have h := fun i => contDiff_pi.1 hid i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hs : ContDiffAt ℝ ∞ (fun y : R4 => euclidNorm y) x :=
    hd.contDiffAt.sqrt (dot4_pos hx).ne'
  exact (hs.inv (slt_euclidNorm_pos hx).ne').smul contDiffAt_id

/-- Directional derivative of `v ↦ e(v)/|e(v)|`. -/
lemma lk_fderiv_normalize_comp {e : Plane → R4} (he : ContDiff ℝ ∞ e) {v : Plane}
    (hne : e v ≠ 0) (w : Plane) :
    fderiv ℝ (fun v => radialNormalize (e v)) v w =
      (euclidNorm (e v))⁻¹ • fderiv ℝ e v w -
        (dot4 (e v) (fderiv ℝ e v w) / euclidNorm (e v) ^ 3) • e v := by
  have hed : DifferentiableAt ℝ e v := (he.differentiable (by simp)) v
  have hEd : DifferentiableAt ℝ (fun v => radialNormalize (e v)) v :=
    ((lk_contDiffAt_normalize hne).differentiableAt (by simp)).comp v hed
  have hl : HasDerivAt (fun r : ℝ => v + r • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hv0 : v = v + (0 : ℝ) • w := by simp
  have h1 := hEd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl hv0
  have he1 := hed.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl hv0
  have h2 := lk_hasDerivAt_normalize he1 (by simpa using hne)
  have := h1.unique h2
  simpa using this

/-- Row operations: normalizing `x` and projecting the other rows. -/
lemma lk_det_normalize (x a b c : R4) (m p q r T : ℝ) :
    Matrix.det (Matrix.of ![m • x, m • (T • a) - p • x, m • b - q • x, m • c - r • x]) =
      m ^ 4 * T * Matrix.det (Matrix.of ![x, a, b, c]) := by
  rw [slt_det4, slt_det4]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Distinct orbits are disjoint -/

lemma lk_traj_eq (hH : ContDiff ℝ ∞ H) (P Q : PeriodicOrbit H) {a b : ℝ}
    (hab : P.x a = Q.x b) (t : ℝ) : Q.x (t + (b - a)) = P.x t := by
  have hxc : Continuous P.x := (trajectory_contDiff hH P.trajectory).continuous
  have hyc : Continuous Q.x := (trajectory_contDiff hH Q.trajectory).continuous
  have hKP : IsCompact (Set.range P.x) :=
    (Function.Periodic.compact_of_continuous P.periodic P.T_pos.ne' hxc)
  have hKQ : IsCompact (Set.range Q.x) :=
    (Function.Periodic.compact_of_continuous Q.periodic Q.T_pos.ne' hyc)
  obtain ⟨R, hR⟩ := (hKP.union hKQ).isBounded.subset_closedBall 0
  have hX : ContDiff ℝ ∞ (hamiltonianVectorField H) := contDiff_hvf hH
  obtain ⟨K, hK⟩ := (hX.contDiffOn (s := Metric.closedBall (0 : R4) R)).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hf : ∀ t, HasDerivAt (fun t => Q.x (t + (b - a)))
      (hamiltonianVectorField H (Q.x (t + (b - a)))) t ∧
      Q.x (t + (b - a)) ∈ Metric.closedBall (0 : R4) R := fun t =>
    ⟨(Q.trajectory.1 _).comp_add_const t (b - a), hR (Or.inr (Set.mem_range_self _))⟩
  have hg : ∀ t, HasDerivAt P.x (hamiltonianVectorField H (P.x t)) t ∧
      P.x t ∈ Metric.closedBall (0 : R4) R := fun t =>
    ⟨P.trajectory.1 t, hR (Or.inl (Set.mem_range_self _))⟩
  have := ODE_solution_unique_univ (v := fun _ => hamiltonianVectorField H)
    (s := fun _ => Metric.closedBall (0 : R4) R) (t₀ := a) (fun _ => hK) hf hg
    (by simp [hab])
  exact congrFun this t

lemma lk_disjoint (hH : ContDiff ℝ ∞ H) (P Q : PeriodicOrbit H) (hQ : Q.image ≠ P.image)
    (a b : ℝ) : P.x a ≠ Q.x b := by
  intro hab
  apply hQ
  have h := lk_traj_eq hH P Q hab
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t - (b - a), ?_⟩
    rw [← h]; congr 1; ring
  · rintro ⟨t, rfl⟩
    exact ⟨t + (b - a), h t⟩

lemma lk_hvf_ne_zero (hS : IsStrictlyStarShapedLevel H) {y : R4} (hy : H y = 1) :
    hamiltonianVectorField H y ≠ 0 := by
  intro h0
  have h := omega0_y_X (H := H) y
  rw [h0] at h
  have : omega0 y 0 = 0 := by simp [omega0]
  linarith [hS.2.2 y hy]

/-! ### The transversality determinant on the disk -/

lemma lk_isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (by fun_prop) continuous_const

lemma lk_openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := fun v hv => by
  simp only [openUnitDisk, closedUnitDisk, Set.mem_setOf_eq] at hv ⊢; exact hv.le

lemma lk_smul_mem_openUnitDisk {v : Plane} (hv : v ∈ openUnitDisk) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • v ∈ openUnitDisk := by
  simp only [openUnitDisk, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
  have h0 := ht.1; have h1 := ht.2
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- `det(e, X_H(e), ∂₀e, ∂₁e)`. -/
def lkDet (H : R4 → ℝ) (e : Plane → R4) (v : Plane) : ℝ :=
  Matrix.det (Matrix.of ![e v, hamiltonianVectorField H (e v),
    fderiv ℝ e v (Pi.single 0 1), fderiv ℝ e v (Pi.single 1 1)])

variable {e : Plane → R4}

lemma lk_dH_fderiv_open (hH : ContDiff ℝ ∞ H) (he : ContDiff ℝ ∞ e)
    (hDS : ∀ v ∈ closedUnitDisk, H (e v) = 1) {v : Plane} (hv : v ∈ openUnitDisk)
    (w : Plane) : fderiv ℝ H (e v) (fderiv ℝ e v w) = 0 := by
  have hev : (H ∘ e) =ᶠ[𝓝 v] fun _ => (1 : ℝ) := by
    filter_upwards [lk_isOpen_openUnitDisk.mem_nhds hv] with q hq
    exact hDS q (lk_openUnitDisk_subset hq)
  have h0 : fderiv ℝ (H ∘ e) v = 0 := by rw [hev.fderiv_eq]; simp
  have hc : fderiv ℝ (H ∘ e) v = (fderiv ℝ H (e v)).comp (fderiv ℝ e v) :=
    fderiv_comp v ((hH.differentiable (by simp)) _) ((he.differentiable (by simp)) _)
  have := congrArg (fun L : Plane →L[ℝ] ℝ => L w) (hc.symm.trans h0)
  simpa using this

lemma lk_det_ne_zero (hS : IsStrictlyStarShapedLevel H) (he : ContDiff ℝ ∞ e)
    (hDS : ∀ v ∈ closedUnitDisk, H (e v) = 1)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) : lkDet H e v ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set x := e v
  set X := hamiltonianVectorField H x
  set a := fderiv ℝ e v (Pi.single 0 1)
  set b := fderiv ℝ e v (Pi.single 1 1)
  have hsum : c 0 • x + c 1 • X + c 2 • a + c 3 • b = 0 := by
    ext j
    have := congrFun hc j
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_four, x, X, a, b] using this
  have hx := hS.2.2 x (hDS v (lk_openUnitDisk_subset hv))
  have hda : fderiv ℝ H x a = 0 := lk_dH_fderiv_open hS.1 he hDS hv _
  have hdb : fderiv ℝ H x b = 0 := lk_dH_fderiv_open hS.1 he hDS hv _
  have hdX : fderiv ℝ H x X = 0 := by
    simp only [X, hamiltonianVectorField_eq]; exact apply_jvec_self _
  have h0' : c 0 = 0 := by
    have := congrArg (fderiv ℝ H x) hsum
    simp only [map_add, map_smul, smul_eq_mul, hda, hdb, hdX, map_zero] at this
    rcases mul_eq_zero.1 (by linarith : c 0 * fderiv ℝ H x x = 0) with h | h
    · exact h
    · exact absurd h hx.ne'
  have hlin : ∀ p q : ℝ, fderiv ℝ e v (![p, q]) = p • a + q • b := fun p q => by
    have hpq : (![p, q] : Plane) = p • (Pi.single 0 1 : Plane) + q • (Pi.single 1 1 : Plane) := by
      ext i; fin_cases i <;> simp
    rw [hpq, map_add, map_smul, map_smul]
  have h1' : c 1 = 0 := by
    by_contra h1
    apply htr v hv
    refine ⟨![-(c 1)⁻¹ * c 2, -(c 1)⁻¹ * c 3], ?_⟩
    show fderiv ℝ e v _ = X
    rw [hlin]
    have hX : c 1 • X = -(c 2 • a + c 3 • b) := by
      rw [h0', zero_smul, zero_add] at hsum
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact hsum
    calc (-(c 1)⁻¹ * c 2) • a + (-(c 1)⁻¹ * c 3) • b = (c 1)⁻¹ • (-(c 2 • a + c 3 • b)) := by
          module
      _ = (c 1)⁻¹ • (c 1 • X) := by rw [hX]
      _ = X := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
  have h23 : fderiv ℝ e v (![c 2, c 3]) = 0 := by
    rw [hlin]
    rw [h0', h1', zero_smul, zero_smul, zero_add, zero_add] at hsum
    exact hsum
  have hz := hinj v (lk_openUnitDisk_subset hv) (h23.trans (map_zero _).symm)
  apply hc0
  ext i
  fin_cases i
  · exact h0'
  · exact h1'
  · simpa using congrFun hz 0
  · simpa using congrFun hz 1

lemma lk_continuous_det (hH : ContDiff ℝ ∞ H) (he : ContDiff ℝ ∞ e) :
    Continuous (lkDet H e) := by
  have h1 : Continuous e := he.continuous
  have h2 : Continuous fun v => hamiltonianVectorField H (e v) :=
    (contDiff_hvf hH).continuous.comp h1
  have hD : Continuous (fderiv ℝ e) := (he.continuous_fderiv (by simp))
  have h3 : Continuous fun v => fderiv ℝ e v (Pi.single 0 1) := hD.clm_apply continuous_const
  have h4 : Continuous fun v => fderiv ℝ e v (Pi.single 1 1) := hD.clm_apply continuous_const
  have c1 := fun i => (continuous_apply i).comp h1
  have c2 := fun i => (continuous_apply i).comp h2
  have c3 := fun i => (continuous_apply i).comp h3
  have c4 := fun i => (continuous_apply i).comp h4
  unfold lkDet
  simp only [slt_det4]
  simp only [Function.comp_def] at c1 c2 c3 c4
  fun_prop

lemma lk_det_mul_pos (hS : IsStrictlyStarShapedLevel H) (he : ContDiff ℝ ∞ e)
    (hDS : ∀ v ∈ closedUnitDisk, H (e v) = 1)
    (hinj : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ e u))
    (htr : ∀ u ∈ openUnitDisk, hamiltonianVectorField H (e u) ∉ Set.range (fderiv ℝ e u))
    {v : Plane} (hv : v ∈ openUnitDisk) : 0 < lkDet H e v * lkDet H e 0 := by
  have hz : (0 : Plane) ∈ openUnitDisk := by simp [openUnitDisk]
  have hD0 := lk_det_ne_zero hS he hDS hinj htr hz
  by_contra hle
  push_neg at hle
  set h : ℝ → ℝ := fun t => lkDet H e (t • v) * lkDet H e 0
  have hc : Continuous h :=
    ((lk_continuous_det hS.1 he).comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h 0 = lkDet H e 0 * lkDet H e 0 := by simp [h]
  have h1 : h 1 = lkDet H e v * lkDet H e 0 := by simp [h]
  have hmem : (0 : ℝ) ∈ Set.Icc (h 1) (h 0) :=
    ⟨by rw [h1]; exact hle, by rw [h0]; exact mul_self_nonneg _⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' zero_le_one hc.continuousOn hmem
  have := lk_det_ne_zero hS he hDS hinj htr (lk_smul_mem_openUnitDisk hv ht)
  exact this (by simpa [h, hD0] using hzero)

end HryniewiczCriterion

/-!
# Reduction of `linksNontrivially_of_isDiskLikeGlobalSectionMap`
-/


noncomputable section

namespace HryniewiczCriterion

theorem linksNontrivially_of_isDiskLikeGlobalSectionMap' (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H)
    (e : Plane → R4) (he : IsDiskLikeGlobalSectionMap H P e) (hQ : Q.image ≠ P.image) :
    LinksNontrivially P Q := by
  have hH := hS.1
  have h2inf : (2 : WithTop ℕ∞) ≤ ∞ := by first | decide | simp | norm_num | exact_mod_cast le_top
  obtain ⟨hemb, hDS', hbdP, htrans, hsec⟩ := he
  obtain ⟨heC, heInj, heD⟩ := hemb
  have hDS : ∀ v ∈ closedUnitDisk, H (e v) = 1 := fun v hv => hDS' ⟨v, hv, rfl⟩
  have he0 : ∀ v ∈ closedUnitDisk, e v ≠ 0 := fun v hv =>
    ne_zero_of_dH_pos (hS.2.2 _ (hDS v hv))
  obtain ⟨Q₀, hQ₀p, hQ₀x, k, hk, hkT⟩ := exists_prime_periodicOrbit_cover H hS Q
  obtain ⟨u, huC, huper, hucirc, hue⟩ :=
    exists_circle_param_of_image_eq H hS P e ⟨heC, heInj, heD⟩ hbdP
  have hT₀ := Q₀.T_pos
  have hQS : ∀ t, H (Q₀.x t) = 1 := Q₀.trajectory.2
  have hPS : ∀ t, H (P.x t) = 1 := P.trajectory.2
  have hQ0 : ∀ t, Q₀.x t ≠ 0 := fun t => ne_zero_of_dH_pos (hS.2.2 _ (hQS t))
  have hP0 : ∀ t, P.x t ≠ 0 := fun t => ne_zero_of_dH_pos (hS.2.2 _ (hPS t))
  have hdisj : ∀ a b, P.x a ≠ Q₀.x b := by
    intro a b; rw [hQ₀x]; exact lk_disjoint hH P Q hQ a b
  have hucD : ∀ s, u s ∈ closedUnitDisk := fun s => by
    have := hucirc s
    simp only [unitCircle, closedUnitDisk, Set.mem_setOf_eq] at this ⊢
    exact this.le
  -- the two loops in `S³`
  set E : Plane → R4 := fun v => radialNormalize (e v) with hE
  set γ : ℝ → R4 := fun t => radialNormalize (Q₀.x (Q₀.T * t)) with hγ
  have hQx : ContDiff ℝ ∞ (fun t => Q₀.x (Q₀.T * t)) :=
    (trajectory_contDiff hH Q₀.trajectory).comp (contDiff_const.mul contDiff_id)
  have hγC : ContDiff ℝ 2 γ :=
    (slt_contDiff_radialNormalize hQx fun t => hQ0 _).of_le h2inf
  have hγper : ∀ t, γ (t + 1) = γ t := fun t => by
    simp only [γ, mul_add, mul_one, Q₀.periodic]
  have hγunit : ∀ t, euclidNorm (γ t) = 1 := fun t => slt_euclidNorm_radialNormalize (hQ0 _)
  have hγinj : ∀ s t, γ s = γ t → ∃ n : ℤ, t = s + n := by
    intro s t h
    have h' := lk_eq_of_normalize_eq hS (hQS _) (hQS _) h
    obtain ⟨n, hn⟩ := slt_orbit_eq_period hH Q₀ hQ₀p h'
    refine ⟨n, ?_⟩
    have h2 : Q₀.T * (t - s) = Q₀.T * n := by linarith
    have := mul_left_cancel₀ hT₀.ne' h2
    linarith
  set U : Set Plane := {v | e v ≠ 0} with hUdef
  have hU : IsOpen U := isOpen_ne_fun heC.continuous continuous_const
  have hDU : closedUnitDisk ⊆ U := fun v hv => he0 v hv
  have hEC : ContDiffOn ℝ 2 E U := fun v hv =>
    (((lk_contDiffAt_normalize hv).comp v heC.contDiffAt).contDiffWithinAt).of_le
      h2inf
  have hEunit : ∀ v ∈ closedUnitDisk, euclidNorm (E v) = 1 := fun v hv =>
    slt_euclidNorm_radialNormalize (he0 v hv)
  have hu2 : ContDiff ℝ 2 u := huC.of_le h2inf
  have hPd : ∀ s, HasDerivAt (fun s => P.x (P.T * s))
      (P.T • hamiltonianVectorField H (P.x (P.T * s))) s := fun s => by
    have hl : HasDerivAt (fun x : ℝ => P.T * x) P.T s := by
      simpa using (hasDerivAt_id s).const_mul P.T
    exact (P.trajectory.1 (P.T * s)).scomp s hl
  have hu' : ∀ s, deriv u s ≠ 0 := by
    intro s h0
    have hd : HasDerivAt (fun s => e (u s)) (fderiv ℝ e (u s) (deriv u s)) s :=
      ((heC.differentiable (by simp)) (u s)).hasFDerivAt.comp_hasDerivAt s
        ((huC.differentiable (by simp)) s).hasDerivAt
    have heq : (fun s => e (u s)) = fun s => P.x (P.T * s) := funext hue
    rw [heq] at hd
    have := hd.unique (hPd s)
    rw [h0, map_zero] at this
    exact lk_hvf_ne_zero hS (hPS _) ((smul_eq_zero.1 this.symm).resolve_left P.T_pos.ne')
  have hbd : ∀ s t, E (u s) ≠ γ t := by
    intro s t h
    have h' : radialNormalize (P.x (P.T * s)) = radialNormalize (Q₀.x (Q₀.T * t)) := by
      rw [← hue s]; exact h
    exact hdisj _ _ (lk_eq_of_normalize_eq hS (hPS _) (hQS _) h')
  -- transversality, with one sign
  have hγd : ∀ t, deriv γ t =
      (euclidNorm (Q₀.x (Q₀.T * t)))⁻¹ •
          (Q₀.T • hamiltonianVectorField H (Q₀.x (Q₀.T * t))) -
        (dot4 (Q₀.x (Q₀.T * t)) (Q₀.T • hamiltonianVectorField H (Q₀.x (Q₀.T * t))) /
          euclidNorm (Q₀.x (Q₀.T * t)) ^ 3) • Q₀.x (Q₀.T * t) := fun t => by
    have hf : HasDerivAt (fun t => Q₀.x (Q₀.T * t))
        (Q₀.T • hamiltonianVectorField H (Q₀.x (Q₀.T * t))) t := by
      have hl : HasDerivAt (fun x : ℝ => Q₀.T * x) Q₀.T t := by
        simpa using (hasDerivAt_id t).const_mul Q₀.T
      exact (Q₀.trajectory.1 (Q₀.T * t)).scomp t hl
    exact (lk_hasDerivAt_normalize hf (hQ0 _)).deriv
  set σ := lkDet H e 0 with hσ
  have htr : ∀ t, ∀ v ∈ closedUnitDisk, E v = γ t →
      0 < σ * Matrix.det (Matrix.of ![γ t, deriv γ t,
        fderiv ℝ E v (Pi.single 0 1), fderiv ℝ E v (Pi.single 1 1)]) := by
    intro t v hv h
    have hx : e v = Q₀.x (Q₀.T * t) := lk_eq_of_normalize_eq hS (hDS v hv) (hQS _) h
    have hvo : v ∈ openUnitDisk := by
      by_contra hno
      have hc : v ∈ unitCircle := by
        simp only [openUnitDisk, closedUnitDisk, unitCircle, Set.mem_setOf_eq] at hv hno ⊢
        push_neg at hno
        linarith
      have hmem : e v ∈ P.image := hbdP ▸ ⟨v, hc, rfl⟩
      obtain ⟨a, ha⟩ := hmem
      exact hdisj a (Q₀.T * t) (ha.trans hx)
    have hpos := lk_det_mul_pos hS heC hDS heD htrans hvo
    rw [hγd t]
    simp only [E]
    rw [lk_fderiv_normalize_comp heC (he0 v hv), lk_fderiv_normalize_comp heC (he0 v hv)]
    simp only [γ]
    rw [← hx]
    simp only [radialNormalize]
    rw [lk_det_normalize]
    have hm : 0 < (euclidNorm (e v))⁻¹ ^ 4 * Q₀.T := by
      have := slt_euclidNorm_pos (he0 v hv)
      positivity
    have hkey : Matrix.det (Matrix.of ![e v, hamiltonianVectorField H (e v),
        fderiv ℝ e v (Pi.single 0 1), fderiv ℝ e v (Pi.single 1 1)]) = lkDet H e v := rfl
    rw [hkey]
    have hr : σ * ((euclidNorm (e v))⁻¹ ^ 4 * Q₀.T * lkDet H e v) =
        ((euclidNorm (e v))⁻¹ ^ 4 * Q₀.T) * (lkDet H e v * lkDet H e 0) := by
      rw [hσ]; ring
    rw [hr]
    exact mul_pos hm hpos
  have hcross : ∃ t, ∃ v ∈ closedUnitDisk, E v = γ t := by
    have hnot : Q₀.x 0 ∉ P.image := by
      rintro ⟨a, ha⟩; exact hdisj a 0 ha
    obtain ⟨⟨t, -, v, hv, hev⟩, -⟩ := hsec Q₀.x Q₀.trajectory hnot 0
    refine ⟨t / Q₀.T, v, hv, ?_⟩
    simp only [E, γ]
    rw [mul_div_cancel₀ t hT₀.ne', hev]
  obtain ⟨N, hN, hNav, n, hn, hG⟩ :=
    gaussLinkingIntegral_ne_zero_of_transverse_disk E U hU hDU hEC hEunit u hu2 huper hucirc hu'
      γ hγC hγper hγunit hγinj hbd σ htr hcross
  -- back to the orbits
  have hEu_eq : (fun s => E (u s)) = fun s => radialNormalize (P.x (P.T * s)) :=
    funext fun s => by simp only [E, hue]
  have hEu : ContDiff ℝ 2 (fun s => E (u s)) := by
    rw [hEu_eq]
    exact (slt_contDiff_radialNormalize
      ((trajectory_contDiff hH P.trajectory).comp (contDiff_const.mul contDiff_id))
      fun s => hP0 _).of_le h2inf
  have hEuper : ∀ s, E (u (s + 1)) = E (u s) := fun s => by rw [huper]
  have hEuunit : ∀ s, euclidNorm (E (u s)) = 1 := fun s => hEunit _ (hucD s)
  have hscale := gaussLinkingIntegral_comp_mul_nat N (fun s => E (u s)) γ hEu hγC hEuper hγper
    hEuunit hγunit hbd hN hNav k
  have hPloop : orbitLoop P = fun s => E (u s) := by
    rw [hEu_eq]; rfl
  have hQloop : orbitLoop Q = fun s => γ (k * s) := by
    funext s
    simp only [orbitLoop, γ, ← hQ₀x, hkT]
    congr 2
    ring
  have hγk : ContDiff ℝ 2 (fun s => γ (k * s)) := hγC.comp (contDiff_const.mul contDiff_id)
  have hPk : Function.Periodic γ ((k : ℝ) * 1) := (show Function.Periodic γ 1 from hγper).nat_mul k
  have hγkper : ∀ s, γ (k * (s + 1)) = γ (k * s) := fun s => by
    rw [mul_add]; exact hPk _
  refine ⟨(k : ℤ) * n, mul_ne_zero (by exact_mod_cast hk.ne') hn, ?_⟩
  rw [hPloop, hQloop]
  exact isLinkingNumber_of_gaussLinkingIntegral_eq _ _ hEu hγk hEuper hγkper hEuunit
    (fun s => hγunit _) (fun s t => hbd s _) N hN (fun s => ⟨(hNav s).1, (hNav _).2⟩) _
    (by rw [hscale, hG]; push_cast; ring)

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P Q : PeriodicOrbit H)
    (e : Plane → R4) (he : IsDiskLikeGlobalSectionMap H P e) (hQ : Q.image ≠ P.image) :
    LinksNontrivially P Q :=
  linksNontrivially_of_isDiskLikeGlobalSectionMap' H hS P Q e he hQ
