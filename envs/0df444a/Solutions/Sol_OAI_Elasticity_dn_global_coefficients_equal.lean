-- Prove2me | solution 1 for OAI.Elasticity.dn_global_coefficients_equal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:25:48.415841+00:00
-- url     : https://prove2.me/submissions/4ca2224f-e0a5-49bc-9e3c-11099f55e0f7

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_Elasticity_dn_conic_comparison
import Theorems.Thm_OAI_ElasticityAugmented_restricted_transports_of_chart_equal
import Theorems.Thm_OAI_ElasticityConic_physical_conic_connections_equal

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

namespace ElasticityConic

lemma theta_null (z₀ z₁ : ℂ) : null (theta z₀ z₁) := by
  simp only [null, dot3, theta, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (z₀ ^ 2 + z₁ ^ 2) ^ 2 * Complex.I_sq

lemma theta_ne_zero {z₀ z₁ : ℂ} (hz : z₀ ≠ 0 ∨ z₁ ≠ 0) : theta z₀ z₁ ≠ 0 := by
  intro h
  have ha := congrFun h 0
  have hb := congrFun h 1
  simp [theta] at ha hb
  have hb' : z₀ ^ 2 + z₁ ^ 2 = 0 := hb
  have hc : z₀ ^ 2 = 0 := by linear_combination (ha + hb') / 2
  have hd : z₁ ^ 2 = 0 := by linear_combination (hb' - ha) / 2
  exact hz.elim (fun hz₀ => hz₀ ((pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0)).mp hc)) (fun hz₁ => hz₁ ((pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0)).mp hd))

/-- The concrete spanning assertion used twice in the source proof. -/
lemma null_dot_zero (v : C3)
    (hv : ∀ θ : C3, θ ≠ 0 → null θ → dotProduct θ v = 0) : v = 0 := by
  have h0 := hv (theta 1 0) (theta_ne_zero (Or.inl one_ne_zero)) (theta_null 1 0)
  have h1 := hv (theta 0 1) (theta_ne_zero (Or.inr one_ne_zero)) (theta_null 0 1)
  have h2 := hv (theta 1 1) (theta_ne_zero (Or.inl one_ne_zero)) (theta_null 1 1)
  simp [theta, Matrix.vecHead, Matrix.vecTail] at h0 h1 h2
  have hv0 : v 0 = 0 := by linear_combination (h0 - h1) / 2
  have hv1 : v 1 = 0 := by
    apply (mul_eq_zero.mp (show Complex.I * v 1 = 0 by linear_combination h0 - hv0)).resolve_left
    exact Complex.I_ne_zero
  have hv2 : v 2 = 0 := by
    simp only [hv1, mul_zero, zero_add] at h2
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  ext i
  fin_cases i <;> assumption

/-- Null directions used to test the entire ambient matrix, without an analytic
argument on projective space. These imply precisely (scalar-ambient-difference). -/
theorem scalar_of_null_annihilator (K : Mat3)
    (hK : ∀ θ : C3, θ ≠ 0 → null θ →
      ∀ p : C3, dotProduct θ p = 0 → dotProduct (K *ᵥ θ) p = 0) :
    ∃ κ : ℂ, K = κ • (1 : Mat3) := by
  have h01p := hK ![1, Complex.I, 0] (by intro h; have h0 := congrFun h 0; norm_num at h0) (by norm_num [null, dot3])
  have h01m := hK ![1, -Complex.I, 0] (by intro h; have h0 := congrFun h 0; norm_num at h0) (by norm_num [null, dot3])
  have h02p := hK ![1, 0, Complex.I] (by intro h; have h0 := congrFun h 0; norm_num at h0) (by norm_num [null, dot3])
  have h02m := hK ![1, 0, -Complex.I] (by intro h; have h0 := congrFun h 0; norm_num at h0) (by norm_num [null, dot3])
  have h12p := hK ![0, 1, Complex.I] (by intro h; have h1 := congrFun h 1; norm_num at h1) (by norm_num [null, dot3])
  have h12m := hK ![0, 1, -Complex.I] (by intro h; have h1 := congrFun h 1; norm_num at h1) (by norm_num [null, dot3])
  have a20 := h01p ![0,0,1] (by simp)
  have b20 := h01m ![0,0,1] (by simp)
  have a10 := h02p ![0,1,0] (by simp)
  have b10 := h02m ![0,1,0] (by simp)
  have a01 := h12p ![1,0,0] (by simp)
  have b01 := h12m ![1,0,0] (by simp)
  simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] at a20 b20 a10 b10 a01 b01
  have k20 : K 2 0 = 0 := by linear_combination (a20 + b20) / 2
  have k21 : K 2 1 = 0 := by
    apply (mul_eq_zero.mp (show K 2 1 * (2 * Complex.I) = 0 by
      linear_combination a20 - b20)).resolve_right
    norm_num
  have k10 : K 1 0 = 0 := by linear_combination (a10 + b10) / 2
  have k12 : K 1 2 = 0 := by
    apply (mul_eq_zero.mp (show K 1 2 * (2 * Complex.I) = 0 by
      linear_combination a10 - b10)).resolve_right
    norm_num
  have k01 : K 0 1 = 0 := by linear_combination (a01 + b01) / 2
  have k02 : K 0 2 = 0 := by
    apply (mul_eq_zero.mp (show K 0 2 * (2 * Complex.I) = 0 by
      linear_combination a01 - b01)).resolve_right
    norm_num
  have d01 := h01p ![1,Complex.I,0] (by norm_num [dot3])
  have d02 := h02p ![1,0,Complex.I] (by norm_num [dot3])
  simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, k01, k02, k10, k12, k20, k21, mul_assoc] at d01 d02
  have k11 : K 1 1 = K 0 0 := by linear_combination -d01
  have k22 : K 2 2 = K 0 0 := by linear_combination -d02
  refine ⟨K 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k01, k02, k10, k12, k20, k21, k11, k22]

end ElasticityConic

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
noncomputable section
open Set Filter Module
open scoped BigOperators Topology

namespace ElasticityFiniteType

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem zero_of_homogeneous_system
    {f : E → F} {A : E → E →L[ℝ] F →L[ℝ] F}
    (hf : Differentiable ℝ f) (hA : Continuous A)
    (hdf : ∀ x v, fderiv ℝ f x v = A x v (f x))
    {x₀ : E} (hzero : f x₀ = 0) : ∀ x, f x = 0 := by
  intro x
  let v := x - x₀
  let c : ℝ → E := fun t => x₀ + t • v
  have hc (t : ℝ) : HasDerivAt c v t := by
    simpa [c] using (hasDerivAt_id t).smul_const v |>.const_add x₀
  have hfc (t : ℝ) : HasDerivAt (fun t => f (c t)) (A (c t) v (f (c t))) t := by
    simpa only [Function.comp_def, hdf] using
      (hf (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hAc : Continuous (fun t => A (c t)) :=
    hA.comp (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (f := fun t => A (c t)) hAc.continuousOn
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖A (c t) v (f (c t))‖ ≤ (C * ‖v‖) * ‖f (c t)‖ := by
    calc
      ‖A (c t) v (f (c t))‖ ≤ ‖A (c t) v‖ * ‖f (c t)‖ :=
        (A (c t) v).le_opNorm _
      _ ≤ (‖A (c t)‖ * ‖v‖) * ‖f (c t)‖ :=
        mul_le_mul_of_nonneg_right ((A (c t)).le_opNorm v) (norm_nonneg _)
      _ ≤ (C * ‖v‖) * ‖f (c t)‖ := by
        gcongr
        exact hC t ⟨ht.1, ht.2.le⟩
  have hstart : f (c 0) = 0 := by simpa [c] using hzero
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (hf.continuous.comp (by fun_prop : Continuous c)).continuousOn
    (fun t _ => (hfc t).hasDerivWithinAt) hstart hbound 1 (by norm_num)
  simpa [c, v] using hz

lemma D_D {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w x : E) :
    D (D f v) w x = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ f y v) x w = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
  simp

lemma D_comm {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w : E) :
    D (D f v) w = D (D f w) v := by
  ext x
  rw [D_D hf, D_D hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) w v

lemma D_add {f g : E → F} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v : E) : D (fun x => f x + g x) v = fun x => D f v x + D g v x := by
  ext x
  simp [D, fderiv_fun_add (hf x) (hg x)]

lemma D_mul {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v : E) : D (fun x => f x * g x) v = fun x => D f v x * g x + f x * D g v x := by
  ext x
  simp [D, fderiv_fun_mul (hf x) (hg x), mul_comm, add_comm]

lemma D_sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (v : E) :
    D (fun x => ∑ i ∈ s, f i x) v = fun x => ∑ i ∈ s, D (f i) v x := by
  ext x
  simp [D, fderiv_fun_sum (fun i hi => (hf i hi) x)]

section CoordinateSystems
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma systemCLM_basis (b : Basis ι ℝ E) (M : E → ι → κ → κ → ℝ)
    (x : E) (s : ι) (w : κ → ℝ) (a : κ) :
    systemCLM b M x (b s) w a = ∑ c, M x s a c * w c := by
  classical
  simp [systemCLM, coordL, matrixCLM, Basis.equivFunL_apply, Finsupp.single_apply]

lemma continuous_systemCLM (b : Basis ι ℝ E) (M : E → ι → κ → κ → ℝ)
    (hM : ∀ s a c, Continuous (fun x => M x s a c)) :
    Continuous (systemCLM b M) := by
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_clm_apply.mpr
  intro w
  apply continuous_pi
  intro a
  have h : Continuous (fun x => ∑ s, coordL b s v * ∑ c, M x s a c * w c) := by
    fun_prop
  simpa [systemCLM, matrixCLM] using h

/-- Coordinate form of the homogeneous-system uniqueness statement. -/
theorem zero_of_coordinate_system (b : Basis ι ℝ E)
    {f : E → κ → ℝ} {M : E → ι → κ → κ → ℝ}
    (hf : Differentiable ℝ f)
    (hM : ∀ s a c, Continuous (fun x => M x s a c))
    (hsystem : ∀ x s a, fderiv ℝ f x (b s) a = ∑ c, M x s a c * f x c)
    {x₀ : E} (hzero : f x₀ = 0) : ∀ x, f x = 0 := by
  apply zero_of_homogeneous_system hf (continuous_systemCLM b M hM) ?_ hzero
  intro x w
  have heq : (fderiv ℝ f x).toLinearMap =
      ((systemCLM b M x).flip (f x)).toLinearMap := by
    apply b.ext
    intro s
    ext a
    simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply,
      systemCLM_basis] using hsystem x s a
  exact congrArg (fun L : E →ₗ[ℝ] (κ → ℝ) => L w) heq

end CoordinateSystems

section Closure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_type_closure (e : ι → E) {η q : E → ℝ}
    {B : ι → ι → ι → E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hB : ∀ i j a, ContDiff ℝ (⊤ : ℕ∞) (B i j a))
    (hess : ∀ i j, D (D η (e i)) (e j) =
      fun x => ∑ a, B i j a x * D η (e a) x + if i = j then q x else 0)
    {s i : ι} (his : i ≠ s) :
    D q (e s) = fun x => ∑ b, C e B s i b x * D η (e b) x + d B s i x * q x := by
  let v : ι → E → ℝ := fun a => D η (e a)
  have hv (a : ι) : ContDiff ℝ (⊤ : ℕ∞) (v a) := contDiff_D hη _
  have hsum (a b : ι) : Differentiable ℝ (fun x => ∑ c, B a b c x * v c x) := by
    exact Differentiable.fun_sum (fun c _ =>
      ((hB a b c).differentiable (by simp)).mul ((hv c).differentiable (by simp)))
  have hdiag : D (v i) (e i) = fun x => ∑ a, B i i a x * v a x + q x := by
    simpa [v] using hess i i
  have hcross : D (v s) (e i) = fun x => ∑ a, B s i a x * v a x := by
    simpa [v, Ne.symm his] using hess s i
  have hthird : D (D (v i) (e i)) (e s) = D (D (v s) (e i)) (e i) := by
    rw [D_comm (hv i) (e i) (e s)]
    change D (D (D η (e i)) (e s)) (e i) = _
    rw [D_comm hη (e i) (e s)]
  rw [hdiag, hcross, D_add (hsum i i) (hq.differentiable (by simp))] at hthird
  have hsumD (a b c : ι) :
      D (fun x => ∑ j, B a b j x * v j x) (e c) =
      fun x => ∑ j, (D (B a b j) (e c) x * v j x + B a b j x * D (v j) (e c) x) := by
    have hd := D_sum (f := fun j x => B a b j x * v j x) Finset.univ
      (fun j _ => ((hB a b j).differentiable (by simp)).mul
        ((hv j).differentiable (by simp))) (e c)
    rw [hd]
    simp_rw [D_mul ((hB a b _).differentiable (by simp)) ((hv _).differentiable (by simp))]
  rw [hsumD, hsumD] at hthird
  ext x
  have hh := congrFun hthird x
  dsimp only at hh
  simp_rw [show ∀ j c, D (v j) (e c) = fun x => ∑ a, B j c a x * v a x +
      if j = c then q x else 0 from hess] at hh
  simp only [C, d]
  -- Expand the finite sums, retaining the unsummed index i throughout.
  simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum, add_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_mul, mul_ite, mul_zero] at hh ⊢
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
  simp_rw [mul_assoc] at hh ⊢
  rw [Finset.sum_comm] at hh
  conv at hh => rhs; rw [Finset.sum_comm]
  dsimp only [v] at hh
  linear_combination hh

omit [DecidableEq ι] in
lemma contDiff_C {B : ι → ι → ι → E → ℝ}
    (e : ι → E) (hB : ∀ i j a, ContDiff ℝ (⊤ : ℕ∞) (B i j a)) (s i b : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (C e B s i b) := by
  have h₁ := contDiff_D (hB s i b) (e i)
  have h₂ := contDiff_D (hB i i b) (e s)
  unfold C
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_d {B : ι → ι → ι → E → ℝ}
    (hB : ∀ i j a, ContDiff ℝ (⊤ : ℕ∞) (B i j a)) (s i : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (d B s i) := by
  exact (hB s i i).sub (hB i i s)

/-- The precise global finite-type endpoint needed after taking the common
exterior extensions. The index type has at least two elements, so there is a
non-diagonal Hessian entry for each direction. -/
theorem finite_type_zero [FiniteDimensional ℝ E] [Nontrivial ι]
    (e : Basis ι ℝ E) {η q : E → ℝ} {B : ι → ι → ι → E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hB : ∀ i j a, ContDiff ℝ (⊤ : ℕ∞) (B i j a))
    (hess : ∀ i j, D (D η (e i)) (e j) =
      fun x => ∑ a, B i j a x * D η (e a) x + if i = j then q x else 0)
    {W : Set E} (hW : IsOpen W) (hne : W.Nonempty) (hz : ∀ x ∈ W, η x = 0) :
    (∀ x, η x = 0) ∧ (∀ x, q x = 0) := by
  classical
  let alt : ι → ι := fun s => Classical.choose (exists_ne s)
  have halt (s : ι) : alt s ≠ s := Classical.choose_spec (exists_ne s)
  let f : E → Option ι → ℝ := fun x a => match a with
    | none => q x
    | some a => D η (e a) x
  let M : E → ι → Option ι → Option ι → ℝ := fun x s a c =>
    match a, c with
    | none, none => d B s (alt s) x
    | none, some b => C e B s (alt s) b x
    | some a, none => if a = s then 1 else 0
    | some a, some b => B a s b x
  have hfc (a : Option ι) : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x a) := by
    cases a with
    | none => exact hq
    | some a => exact contDiff_D hη _
  have hf : Differentiable ℝ f := differentiable_pi.mpr fun a =>
    (hfc a).differentiable (by simp)
  have hM (s : ι) (a c : Option ι) : Continuous (fun x => M x s a c) := by
    cases a <;> cases c
    · exact (contDiff_d hB s (alt s)).continuous
    · exact (contDiff_C e hB s (alt s) _).continuous
    · exact continuous_const
    · exact (hB _ _ _).continuous
  have hsys (x : E) (s : ι) (a : Option ι) :
      fderiv ℝ f x (e s) a = ∑ c, M x s a c * f x c := by
    have hd : fderiv ℝ f x (e s) a = D (fun y => f y a) (e s) x := by
      simp [D, fderiv_apply (hf x) a]
    rw [hd]
    cases a with
    | none =>
      have h := congrFun (finite_type_closure e hη hq hB hess (halt s)) x
      simpa [f, M, Fintype.sum_option, add_comm] using h
    | some a =>
      have h := congrFun (hess a s) x
      simpa [f, M, Fintype.sum_option, ite_mul, add_comm] using h
  obtain ⟨x₀, hx₀⟩ := hne
  have hevent : η =ᶠ[𝓝 x₀] (fun _ => 0) :=
    Filter.eventually_of_mem (hW.mem_nhds hx₀) hz
  have hgrad (a : ι) : D η (e a) =ᶠ[𝓝 x₀] (fun _ => 0) := by
    filter_upwards [hevent.fderiv (𝕜 := ℝ)] with x hx
    simp [D, hx]
  have hfzero : f x₀ = 0 := by
    ext a
    cases a with
    | some a => exact (hgrad a).self_of_nhds
    | none =>
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      have hi := congrFun (hess i i) x₀
      have hdi : D (D η (e i)) (e i) x₀ = 0 := by
        simp [D, (hgrad i).fderiv_eq]
      have hv (a : ι) : D η (e a) x₀ = 0 := (hgrad a).self_of_nhds
      simpa [hdi, hv] using hi.symm
  have hall := zero_of_coordinate_system e hf hM hsys hfzero
  have hqzero (x : E) : q x = 0 := congrFun (hall x) none
  have hderiv (x : E) : fderiv ℝ η x = 0 := by
    have he : (fderiv ℝ η x).toLinearMap = (0 : E →ₗ[ℝ] ℝ) := by
      apply e.ext
      intro a
      exact congrFun (hall x) (some a)
    exact DFunLike.coe_injective (congrArg (fun L : E →ₗ[ℝ] ℝ => (L : E → ℝ)) he)
  constructor
  · apply zero_of_homogeneous_system (hη.differentiable (by simp))
      (A := fun _ => 0) continuous_const ?_ (hz x₀ hx₀)
    intro x v
    simp [hderiv x]
  · exact hqzero

end Closure

end ElasticityFiniteType

namespace ElasticityRecovery
open Module ElasticityFiniteType ElasticityConic

lemma D_sub {f g : X → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v : X) : D (fun x => f x - g x) v = fun x => D f v x - D g v x := by
  ext x
  simp [D, fderiv_fun_sub (hf x) (hg x)]

lemma grad_sub {f g : X → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (x : X) (i : Fin 3) : grad (fun x => f x - g x) x i = grad f x i - grad g x i := by
  exact congrFun (D_sub hf hg (basis i)) x

lemma dir_sub {f g : X → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (θ : C3) (x : X) : dir θ (fun x => f x - g x) x = dir θ f x - dir θ g x := by
  simp [dir, grad_sub hf hg, dotProduct, Finset.sum_sub_distrib, mul_sub]

lemma fderiv_zero_of_null (f : X → ℝ) (x : X)
    (hf : ∀ θ : C3, θ ≠ 0 → null θ → dir θ f x = 0) : fderiv ℝ f x = 0 := by
  have hv := null_dot_zero (fun i => (grad f x i : ℂ)) hf
  have hb (i : Fin 3) : grad f x i = 0 := by
    exact Complex.ofReal_eq_zero.mp (congrFun hv i)
  have he : (fderiv ℝ f x).toLinearMap = (0 : X →ₗ[ℝ] ℝ) := by
    apply basis.ext
    exact hb
  exact DFunLike.coe_injective (congrArg (fun L : X →ₗ[ℝ] ℝ => (L : X → ℝ)) he)

lemma zero_of_null_derivatives {f : X → ℝ}
    (hf : Differentiable ℝ f)
    (hd : ∀ x θ, θ ≠ 0 → null θ → dir θ f x = 0)
    {x₀ : X} (hz : f x₀ = 0) : ∀ x, f x = 0 := by
  apply zero_of_homogeneous_system hf (A := fun _ => 0) continuous_const ?_ hz
  intro x v
  simp [fderiv_zero_of_null f x (hd x)]

lemma real_scalar_of_null_annihilator (K : RMat)
    (hK : ∀ θ : C3, θ ≠ 0 → null θ → ∀ p : C3, dotProduct θ p = 0 →
      dotProduct ((fun i j => (K i j : ℂ)) *ᵥ θ) p = 0) :
    ∀ i j, K i j = if i = j then K 0 0 else 0 := by
  obtain ⟨κ, hκ⟩ := scalar_of_null_annihilator _ hK
  have hk : κ = (K 0 0 : ℂ) := by
    simpa using (congrArg (fun M : Mat3 => M 0 0) hκ).symm
  intro i j
  have he := congrArg (fun M : Mat3 => M i j) hκ
  apply Complex.ofReal_injective
  simpa [hk, Matrix.one_apply, apply_ite] using he

lemma contDiff_log {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ x, 0 < f x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.log (f x)) :=
  hf.log (fun x => (hp x).ne')

lemma contDiff_logRatio {m k : X → ℝ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hmp : ∀ x, 0 < m x) (hkp : ∀ x, 0 < k x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.log (k x / (k x + m x))) := by
  exact contDiff_log (hk.div (hk.add hm) (fun x => (add_pos (hkp x) (hmp x)).ne'))
    (fun x => div_pos (hkp x) (add_pos (hkp x) (hmp x)))

lemma ratio_equal {m₁ k₁ m₂ k₂ : X → ℝ}
    (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁) (hk₁ : ContDiff ℝ (⊤ : ℕ∞) k₁)
    (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂) (hk₂ : ContDiff ℝ (⊤ : ℕ∞) k₂)
    (hmp₁ : ∀ x, 0 < m₁ x) (hkp₁ : ∀ x, 0 < k₁ x)
    (hmp₂ : ∀ x, 0 < m₂ x) (hkp₂ : ∀ x, 0 < k₂ x)
    (ht : EqualRestrictedTransports m₁ k₁ m₂ k₂)
    {x₀ : X} (hm₀ : m₁ x₀ = m₂ x₀) (hk₀ : k₁ x₀ = k₂ x₀) :
    ∀ x, k₁ x / (k₁ x + m₁ x) = k₂ x / (k₂ x + m₂ x) := by
  let ρ₁ := fun x => Real.log (k₁ x / (k₁ x + m₁ x))
  let ρ₂ := fun x => Real.log (k₂ x / (k₂ x + m₂ x))
  have h₁ := (contDiff_logRatio hm₁ hk₁ hmp₁ hkp₁).differentiable (by simp)
  have h₂ := (contDiff_logRatio hm₂ hk₂ hmp₂ hkp₂).differentiable (by simp)
  have hz : ∀ x, ρ₁ x - ρ₂ x = 0 := by
    apply zero_of_null_derivatives (h₁.sub h₂) ?_ (x₀ := x₀) ?_
    · intro x θ hn hnull
      change dir θ (fun y => ρ₁ y - ρ₂ y) x = 0
      rw [dir_sub h₁ h₂]
      exact sub_eq_zero.mpr (ht x θ hn hnull).1
    · simp [hm₀, hk₀]
  intro x
  apply Real.log_injOn_pos
    (div_pos (hkp₁ x) (add_pos (hkp₁ x) (hmp₁ x)))
    (div_pos (hkp₂ x) (add_pos (hkp₂ x) (hmp₂ x)))
  exact sub_eq_zero.mp (hz x)

lemma ratios_algebra {m₁ k₁ m₂ k₂ : ℝ}
    (hm₁ : 0 < m₁) (hk₁ : 0 < k₁) (hm₂ : 0 < m₂) (hk₂ : 0 < k₂)
    (h : k₁ / (k₁ + m₁) = k₂ / (k₂ + m₂)) :
    m₁ / (k₁ + m₁) = m₂ / (k₂ + m₂) ∧ k₁ / m₁ = k₂ / m₂ := by
  have hd₁ := (add_pos hk₁ hm₁).ne'
  have hd₂ := (add_pos hk₂ hm₂).ne'
  have hcross := (div_eq_div_iff hd₁ hd₂).mp h
  constructor
  · apply (div_eq_div_iff hd₁ hd₂).mpr
    nlinarith
  · apply (div_eq_div_iff hm₁.ne' hm₂.ne').mpr
    nlinarith

lemma hessian_sub {f g : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : X) (i j : Fin 3) :
    hessian (fun x => f x - g x) x i j = hessian f x i j - hessian g x i j := by
  unfold hessian
  rw [D_sub (hf.differentiable (by simp)) (hg.differentiable (by simp)),
    D_sub ((contDiff_D hf _).differentiable (by simp))
      ((contDiff_D hg _).differentiable (by simp))]

lemma contDiff_grad {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => grad f x i) := contDiff_D hf _

lemma contDiff_hessian {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => hessian f x i j) := contDiff_D (contDiff_D hf _) _

lemma contDiff_QMatrix {m k : X → ℝ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hmp : ∀ x, 0 < m x) (hkp : ∀ x, 0 < k x) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => QMatrix m k x i j) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => m x / (k x + m x)) :=
    hm.div (hk.add hm) (fun x => (add_pos (hkp x) (hmp x)).ne')
  have hg (a : Fin 3) := contDiff_grad (contDiff_log hm hmp) a
  have ht (a : Fin 3) := contDiff_grad (contDiff_log hk hkp) a
  have hh := contDiff_hessian (contDiff_log hm hmp) i j
  unfold QMatrix
  fun_prop

lemma recovery_entry {c g₁ᵢ g₁ⱼ g₂ᵢ g₂ⱼ t₁ t₂ H₁ H₂ κ δ : ℝ}
    (hc : c ≠ 0) (ht : t₁ - t₂ = g₁ⱼ - g₂ⱼ)
    (hQ : (1 / 2 : ℝ) * ((c * t₁ - (1 / 2 : ℝ) * g₁ⱼ) * g₁ᵢ - c * H₁) -
      (1 / 2 : ℝ) * ((c * t₂ - (1 / 2 : ℝ) * g₂ⱼ) * g₂ᵢ - c * H₂) = κ * δ) :
    H₁ - H₂ = ((c - (1 / 2 : ℝ)) / c) * g₁ᵢ * (g₁ⱼ - g₂ⱼ) +
      (((c - (1 / 2 : ℝ)) / c) * g₂ⱼ + (t₂ - g₂ⱼ)) * (g₁ᵢ - g₂ᵢ) +
      (-2 * κ / c) * δ := by
  have ht' : t₁ = t₂ + (g₁ⱼ - g₂ⱼ) := by linarith
  rw [ht'] at hQ
  field_simp [hc]
  linear_combination -4 * hQ

/-- The final coefficient-recovery step, with its genuine intermediate transport
hypothesis explicit. This is not the main DN uniqueness theorem. -/
theorem coefficients_equal_of_restricted_transports
    {m₁ k₁ m₂ k₂ : X → ℝ}
    (hm₁ : ContDiff ℝ (⊤ : ℕ∞) m₁) (hk₁ : ContDiff ℝ (⊤ : ℕ∞) k₁)
    (hm₂ : ContDiff ℝ (⊤ : ℕ∞) m₂) (hk₂ : ContDiff ℝ (⊤ : ℕ∞) k₂)
    (hmp₁ : ∀ x, 0 < m₁ x) (hkp₁ : ∀ x, 0 < k₁ x)
    (hmp₂ : ∀ x, 0 < m₂ x) (hkp₂ : ∀ x, 0 < k₂ x)
    (ht : EqualRestrictedTransports m₁ k₁ m₂ k₂)
    {W : Set X} (hW : IsOpen W) (hne : W.Nonempty)
    (hmW : ∀ x ∈ W, m₁ x = m₂ x) (hkW : ∀ x ∈ W, k₁ x = k₂ x) :
    m₁ = m₂ ∧ k₁ = k₂ := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hr := ratio_equal hm₁ hk₁ hm₂ hk₂ hmp₁ hkp₁ hmp₂ hkp₂ ht
    (hmW x₀ hx₀) (hkW x₀ hx₀)
  have hc (x : X) := (ratios_algebra (hmp₁ x) (hkp₁ x) (hmp₂ x) (hkp₂ x) (hr x)).1
  have hb (x : X) := (ratios_algebra (hmp₁ x) (hkp₁ x) (hmp₂ x) (hkp₂ x) (hr x)).2
  let l₁ := fun x => Real.log (m₁ x)
  let l₂ := fun x => Real.log (m₂ x)
  let t₁ := fun x => Real.log (k₁ x)
  let t₂ := fun x => Real.log (k₂ x)
  have hl₁ : ContDiff ℝ (⊤ : ℕ∞) l₁ := contDiff_log hm₁ hmp₁
  have hl₂ : ContDiff ℝ (⊤ : ℕ∞) l₂ := contDiff_log hm₂ hmp₂
  have ht₁ : ContDiff ℝ (⊤ : ℕ∞) t₁ := contDiff_log hk₁ hkp₁
  have ht₂ : ContDiff ℝ (⊤ : ℕ∞) t₂ := contDiff_log hk₂ hkp₂
  have heq : (fun x => t₁ x - l₁ x) = (fun x => t₂ x - l₂ x) := by
    ext x
    have he := congrArg Real.log (hb x)
    simpa [Real.log_div (hkp₁ x).ne' (hmp₁ x).ne',
      Real.log_div (hkp₂ x).ne' (hmp₂ x).ne'] using he
  have htg (x : X) (j : Fin 3) : grad t₁ x j - grad t₂ x j =
      grad l₁ x j - grad l₂ x j := by
    have he := congrArg (fun f : X → ℝ => grad f x j) heq
    rw [grad_sub (ht₁.differentiable (by simp)) (hl₁.differentiable (by simp)),
      grad_sub (ht₂.differentiable (by simp)) (hl₂.differentiable (by simp))] at he
    linarith
  let K : X → RMat := fun x i j => QMatrix m₁ k₁ x i j - QMatrix m₂ k₂ x i j
  let κ : X → ℝ := fun x => K x 0 0
  have hK (x : X) : ∀ i j, K x i j = if i = j then κ x else 0 := by
    apply real_scalar_of_null_annihilator
    intro θ hn hnull p hp
    have he := (ht x θ hn hnull).2 p hp
    simpa [K, Q, dotProduct, Matrix.mulVec, sub_mul, Finset.sum_sub_distrib]
      using sub_eq_zero.mpr he
  have hKc (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j) :=
    (contDiff_QMatrix hm₁ hk₁ hmp₁ hkp₁ i j).sub
      (contDiff_QMatrix hm₂ hk₂ hmp₂ hkp₂ i j)
  let c := fun x => m₁ x / (k₁ x + m₁ x)
  have hcp (x : X) : 0 < c x := div_pos (hmp₁ x) (add_pos (hkp₁ x) (hmp₁ x))
  have hcc : ContDiff ℝ (⊤ : ℕ∞) c :=
    hm₁.div (hk₁.add hm₁) (fun x => (add_pos (hkp₁ x) (hmp₁ x)).ne')
  let α := fun x => (c x - (1 / 2 : ℝ)) / c x
  let q := fun x => -2 * κ x / c x
  let η := fun x => l₁ x - l₂ x
  let B : Fin 3 → Fin 3 → Fin 3 → X → ℝ := fun i j a x =>
    α x * grad l₁ x i * (if j = a then 1 else 0) +
      (α x * grad l₂ x j + (grad t₂ x j - grad l₂ x j)) * (if i = a then 1 else 0)
  have hα : ContDiff ℝ (⊤ : ℕ∞) α := (hcc.sub contDiff_const).div hcc (fun x => (hcp x).ne')
  have hq : ContDiff ℝ (⊤ : ℕ∞) q :=
    (contDiff_const.mul (hKc 0 0)).div hcc (fun x => (hcp x).ne')
  have hB (i j a : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (B i j a) := by
    have hg₁ := contDiff_grad hl₁ i
    have hg₂ := contDiff_grad hl₂ j
    have hgt := contDiff_grad ht₂ j
    dsimp [B]
    fun_prop
  have hess (i j : Fin 3) : D (D η (basis i)) (basis j) =
      fun x => (∑ a, B i j a x * D η (basis a) x) + (if i = j then q x else 0) := by
    ext x
    have hQ := hK x i j
    have hc' : m₂ x / (k₂ x + m₂ x) = c x := (hc x).symm
    change QMatrix m₁ k₁ x i j - QMatrix m₂ k₂ x i j = _ at hQ
    simp only [QMatrix, hc'] at hQ
    have hδ : (if i = j then κ x else 0) = κ x * (if i = j then (1 : ℝ) else 0) := by
      split_ifs <;> simp
    rw [hδ] at hQ
    have hh := recovery_entry (hcp x).ne' (htg x j) hQ
    change hessian η x i j = _
    rw [hessian_sub hl₁ hl₂]
    change hessian l₁ x i j - hessian l₂ x i j = _ at hh
    rw [hh]
    have hv (a : Fin 3) : D η (basis a) x = grad l₁ x a - grad l₂ x a :=
      grad_sub (hl₁.differentiable (by simp)) (hl₂.differentiable (by simp)) x a
    simp only [B, hv, add_mul, mul_assoc, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    rfl
  have hηzero : ∀ x ∈ W, η x = 0 := by
    intro x hx
    simp [η, l₁, l₂, hmW x hx]
  have hz := (finite_type_zero basis (hl₁.sub hl₂) hq hB hess hW ⟨x₀, hx₀⟩ hηzero).1
  have hm : m₁ = m₂ := by
    ext x
    apply Real.log_injOn_pos (hmp₁ x) (hmp₂ x)
    exact sub_eq_zero.mp (hz x)
  refine ⟨hm, ?_⟩
  ext x
  have he := hb x
  rw [hm] at he
  exact (div_left_inj' (hmp₂ x).ne').mp he

end ElasticityRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO

open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

lemma fiveCutoff_one (R : ℝ) (hR : 1≤R) (i : Fin 5) {x : X}
    (hx : x∈Metric.closedBall 0 (R+(i.val : ℝ)+1)) : fiveCutoff R hR i x=1 := by
  have hh := (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)).one_of_mem_closedBall hx
  unfold fiveCutoff
  rw [hh,Complex.ofReal_one]
end ElasticityCGO

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Rigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace Elasticity
open ElasticityAugmented ElasticityCGO ElasticityConic
open ElasticityCoeffBounds (ExteriorConstant)

lemma physicalChartMatrix_congr_k (b : Bool) (z : ℂ) (k₀ k₁ r : Smooth)
    (e : k₀=k₁) (hr : ∀ x,(r : X → ℂ) x≠0)
    (hk₀ : ∀ x,(k₀ : X → ℂ) x≠0) (hk₁ : ∀ x,(k₁ : X → ℂ) x≠0)
    (hl₀ : ∀ x,((k₀+r*r : Smooth) : X → ℂ) x≠0)
    (hl₁ : ∀ x,((k₁+r*r : Smooth) : X → ℂ) x≠0) :
    physicalChartMatrix b z k₀ r hr hk₀ hl₀ = physicalChartMatrix b z k₁ r hr hk₁ hl₁ := by
  subst k₁
  rfl

/-- The global transport-matching implication for a genuine common exterior.
Its only inverse-data hypothesis is equality of the physical DN maps. -/
theorem dn_global_coefficients_equal_oai {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    lam 0=lam 1 ∧ m 0=m 1 := by
  have hK : IsCompact (closure Ω) := hOB.isCompact_closure
  obtain ⟨R,hR,hKR⟩ := hOB.closure.subset_closedBall_lt 1 (0 : X)
  have hr₀ : 1≤R := hR.le
  let kr := fun q x => lam q x+m q x
  have hks (q) : ContDiff ℝ (⊤ : ℕ∞) (kr q) := (hl q).add (hm q)
  have hkp (q x) : 0 < kr q x := by dsimp [kr]; have hh := hp q x; linarith
  let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
  let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
  have hr (q x) : (r q : X → ℂ) x≠0 := positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1) x
  have hk (q x) : (k q : X → ℂ) x≠0 := by
    change (lam q x : ℂ)+(m q x : ℂ)≠0
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (hkp q x).ne'
  have hL (q x) : ((k q+r q*r q : Smooth) : X → ℂ) x≠0 := by
    have hrr : r q*r q=smoothOfReal (m q) (hm q) := positiveRoot_square (m q) (hm q) (fun x => (hp q x).1)
    rw [hrr]
    change (lam q x : ℂ)+(m q x : ℂ)+(m q x : ℂ)≠0
    rw [← Complex.ofReal_add,← Complex.ofReal_add]
    apply Complex.ofReal_ne_zero.mpr
    have hh := hp q x
    linarith
  choose G hs hge using (fun b z => dn_conic_comparison hΩ hOB R hr₀ hKR lam m hl hm hp hcll hclm he hDN b z hk hL)
  have hne : (closure Ω)ᶜ.Nonempty := Set.nonempty_compl.mpr hK.ne_univ
  obtain ⟨x₀,hx₀⟩ := hne
  let χ : Smooth := ⟨fiveCutoff R hr₀ 0,fiveCutoff_smooth R hr₀ 0⟩
  have hχ1 (x) (hx : x∈closure Ω) : (χ : X → ℂ) x=1 := by
    apply fiveCutoff_one R hr₀ 0
    simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using
      Metric.closedBall_subset_closedBall (by linarith : R≤R+1) (hKR hx)
  have hek : EqOn (k 0 : X → ℂ) (k 1) (closure Ω)ᶜ := by
    intro x hx
    have hh := he x (fun hh => hx (subset_closure hh))
    change (lam 0 x : ℂ)+(m 0 x : ℂ)=(lam 1 x : ℂ)+(m 1 x : ℂ)
    rw [hh.1,hh.2]
  have her : EqOn (r 0 : X → ℂ) (r 1) (closure Ω)ᶜ := by
    intro x hx
    have hh := he x (fun hh => hx (subset_closure hh))
    change (Real.sqrt (m 0 x) : ℂ)=(Real.sqrt (m 1 x) : ℂ)
    rw [hh.2]
  have hM := physical_conic_connections_equal k r hr hk hL hK χ
    (fiveCutoff_compact R hr₀ 0) hχ1 x₀ hx₀ hek her G hs hge
  have ht : ElasticityRecovery.EqualRestrictedTransports (m 0) (kr 0) (m 1) (kr 1) := by
    apply restricted_transports_of_chart_equal m kr hm hks (fun q x => (hp q x).1) hkp
    intro b z
    have hEq (q : Fin 2) : smoothOfReal (kr q) (hks q)=k q :=
      (smoothOfReal_add (lam q) (m q) (hl q) (hm q)).symm
    exact (physicalChartMatrix_congr_k b z _ _ _ (hEq 0) _ _ _ _ _).trans
      ((hM b z).trans (physicalChartMatrix_congr_k b z _ _ _ (hEq 1) _ _ _ _ _).symm)
  have hmk := ElasticityRecovery.coefficients_equal_of_restricted_transports
    (hm 0) (hks 0) (hm 1) (hks 1) (fun x => (hp 0 x).1) (hkp 0)
    (fun x => (hp 1 x).1) (hkp 1) ht isClosed_closure.isOpen_compl ⟨x₀,hx₀⟩
    (fun x hx => (he x (fun hh => hx (subset_closure hh))).2)
    (fun x hx => by dsimp [kr]; rw [(he x (fun hh => hx (subset_closure hh))).1,(he x (fun hh => hx (subset_closure hh))).2])
  refine ⟨?_,hmk.1⟩
  funext x
  have hh := congrFun hmk.2 x
  have hm' := congrFun hmk.1 x
  dsimp [kr] at hh
  linarith
end Elasticity

end
end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.dn_global_coefficients_equal_oai := @OAI.Elasticity.dn_global_coefficients_equal_oai
