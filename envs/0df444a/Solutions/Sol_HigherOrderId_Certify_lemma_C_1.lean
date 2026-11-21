-- Prove2me | solution 1 for HigherOrderId.Certify.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T20:41:03.294366+00:00
-- url     : https://prove2.me/submissions/dd2a50fe-e0cc-4274-b4db-7bd0752ebe3c

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_GaussTest

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.C1
open HigherOrderId.Certify

/-- The standard Gaussian product measure on coordinates. -/
noncomputable abbrev piN (D : ℕ) : Measure (Fin D → ℝ) :=
  Measure.pi (fun _ : Fin D ↦ gaussianReal 0 1)

lemma sqrt_herm {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) : (CFC.sqrt S).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).1

/-- Eigenvector basis of `√S`. -/
noncomputable abbrev bas {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) :
    OrthonormalBasis (Fin D) ℝ (EuclideanSpace ℝ (Fin D)) :=
  (sqrt_herm S).eigenvectorBasis

/-- Eigenvalues of `√S`. -/
noncomputable abbrev mu {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) : Fin D → ℝ :=
  (sqrt_herm S).eigenvalues

/-- Synthesis map of the eigenbasis. -/
noncomputable def V {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (y : Fin D → ℝ) :
    EuclideanSpace ℝ (Fin D) :=
  ∑ i, y i • bas S i

lemma measurable_V {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) : Measurable (V S) := by
  unfold V; fun_prop

lemma inner_V {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (y : Fin D → ℝ) (j : Fin D) :
    inner ℝ (bas S j) (V S y) = y j := by
  simp [V, inner_sum, inner_smul_right, (bas S).inner_eq_ite]

lemma norm_V_sq {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (y : Fin D → ℝ) :
    ‖V S y‖ ^ 2 = ∑ i, y i ^ 2 := by
  rw [← (bas S).sum_sq_norm_inner_right]
  simp [inner_V]

lemma V_coord {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (θ : EuclideanSpace ℝ (Fin D)) :
    V S (fun i ↦ inner ℝ (bas S i) θ) = θ := (bas S).sum_repr' θ

lemma sqrt_bas {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (i : Fin D) :
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) (bas S i) = mu S i • bas S i := by
  apply PiLp.ext
  intro j
  have := congrFun ((sqrt_herm S).mulVec_eigenvectorBasis i) j
  simpa [ofLp_toEuclideanCLM] using this

/-- Spectral representation of `N(θ, S)`. -/
lemma mvg_eq {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (θ : EuclideanSpace ℝ (Fin D)) :
    multivariateGaussian θ S =
      (piN D).map (fun x ↦ V S (fun i ↦ inner ℝ (bas S i) θ + mu S i * x i)) := by
  rw [multivariateGaussian, stdGaussian_eq_map_pi_orthonormalBasis (bas S),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, map_sum, map_smul, sqrt_bas]
  conv_lhs => rw [← V_coord S θ]
  simp only [V, smul_smul, ← Finset.sum_add_distrib, add_smul]
  congr 1; funext i; ring_nf

lemma integral_mvg {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (θ : EuclideanSpace ℝ (Fin D))
    (φ : EuclideanSpace ℝ (Fin D) → ℝ) (hφ : Measurable φ) :
    ∫ x, φ x ∂(multivariateGaussian θ S) =
      ∫ x, φ (V S (fun i ↦ inner ℝ (bas S i) θ + mu S i * x i)) ∂(piN D) := by
  rw [mvg_eq, integral_map _ hφ.aestronglyMeasurable]
  exact ((measurable_V S).comp (by fun_prop)).aemeasurable

/-! Traces. -/

lemma spec_tr {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) (hW : Wᵀ * W = 1)
    (f : n → ℝ) : (W * Matrix.diagonal f * Wᵀ).trace = ∑ i, f i := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one,
    Matrix.trace_diagonal]

lemma spec_mul {n : Type*} [Fintype n] [DecidableEq n] (W : Matrix n n ℝ) (hW : Wᵀ * W = 1)
    (f g : n → ℝ) :
    (W * Matrix.diagonal f * Wᵀ) * (W * Matrix.diagonal g * Wᵀ) =
      W * Matrix.diagonal (fun i ↦ f i * g i) * Wᵀ := by
  rw [show W * diagonal f * Wᵀ * (W * diagonal g * Wᵀ) =
      W * diagonal f * (Wᵀ * W) * diagonal g * Wᵀ by simp only [Matrix.mul_assoc], hW,
    Matrix.mul_one, Matrix.mul_assoc W, diagonal_mul_diagonal]

lemma sqrt_spec {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) :
    ∃ W : Matrix (Fin D) (Fin D) ℝ, Wᵀ * W = 1 ∧
      CFC.sqrt S = W * Matrix.diagonal (mu S) * Wᵀ := by
  have hM := sqrt_herm S
  refine ⟨((sqrt_herm S).eigenvectorUnitary : Matrix (Fin D) (Fin D) ℝ), ?_, ?_⟩
  · have := Unitary.coe_star_mul_self (sqrt_herm S).eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have := (sqrt_herm S).spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma trace_eq {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef) :
    S.trace = ∑ i, mu S i ^ 2 := by
  obtain ⟨W, hW, hR⟩ := sqrt_spec S
  have h := CFC.sqrt_mul_sqrt_self S hS.nonneg
  conv_lhs => rw [← h, hR, spec_mul W hW, spec_tr W hW]
  simp [sq]

lemma frob_eq {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef) :
    frobInner S S = ∑ i, mu S i ^ 4 := by
  obtain ⟨W, hW, hR⟩ := sqrt_spec S
  have h := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hT : frobInner S S = (S * Sᵀ).trace := by
    simp [frobInner, Matrix.trace, Matrix.mul_apply]
  have hSt : Sᵀ = S := by
    exact (Matrix.conjTranspose_eq_transpose_of_trivial S).symm.trans hS.1
  rw [hT, hSt]
  conv_lhs => rw [← h, hR, spec_mul W hW, spec_mul W hW, spec_tr W hW]
  congr 1; funext i; ring

end HigherOrderId.Certify.Dev.C1
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.C1
open HigherOrderId.Certify

/-! ### Moments of the standard Gaussian -/

lemma hasDerivAt_pe (p p' : ℝ → ℝ) (t : ℝ) (hp : HasDerivAt p (p' t) t) :
    HasDerivAt (fun s ↦ p s * Real.exp (s ^ 2 / 2))
      ((p' t + t * p t) * Real.exp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
    exact ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by norm_num)
  have h2 := h1.exp
  exact (hp.mul h2).congr_deriv (by ring)

lemma deriv_pe (p p' : ℝ → ℝ) (hp : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun s ↦ p s * Real.exp (s ^ 2 / 2)) =
      fun t ↦ (p' t + t * p t) * Real.exp (t ^ 2 / 2) := by
  funext t; exact (hasDerivAt_pe p p' t (hp t)).deriv

lemma hasDerivAt_cubic (a b c d t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ a + b * s + c * s ^ 2 + d * s ^ 3)
      (b + 2 * c * t + 3 * d * t ^ 2) t := by
  have h1 := (hasDerivAt_id' t).const_mul b
  have h2 := (hasDerivAt_pow 2 t).const_mul c
  have h3 := (hasDerivAt_pow 3 t).const_mul d
  exact (((h1.const_add a).add h2).add h3).congr_deriv (by norm_num; ring)

lemma deriv_cubic (a b c d : ℝ) :
    deriv (fun s ↦ (a + b * s + c * s ^ 2 + d * s ^ 3) * Real.exp (s ^ 2 / 2)) =
      fun t ↦ (b + 2 * c * t + 3 * d * t ^ 2 + t * (a + b * t + c * t ^ 2 + d * t ^ 3)) *
        Real.exp (t ^ 2 / 2) :=
  deriv_pe _ _ (fun t ↦ hasDerivAt_cubic a b c d t)

lemma mgf_N01 : mgf id (gaussianReal 0 1) =
    fun t ↦ (1 + 0 * t + 0 * t ^ 2 + 0 * t ^ 3) * Real.exp (t ^ 2 / 2) := by
  rw [mgf_id_gaussianReal]; funext t; simp

lemma iter_mgf :
    iteratedDeriv 1 (mgf id (gaussianReal 0 1)) 0 = 0 ∧
    iteratedDeriv 2 (mgf id (gaussianReal 0 1)) 0 = 1 ∧
    iteratedDeriv 3 (mgf id (gaussianReal 0 1)) 0 = 0 ∧
    iteratedDeriv 4 (mgf id (gaussianReal 0 1)) 0 = 3 := by
  have d1 : iteratedDeriv 1 (mgf id (gaussianReal 0 1)) =
      fun t ↦ (0 + 1 * t + 0 * t ^ 2 + 0 * t ^ 3) * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_one, mgf_N01, deriv_cubic]; funext t; ring
  have d2 : iteratedDeriv 2 (mgf id (gaussianReal 0 1)) =
      fun t ↦ (1 + 0 * t + 1 * t ^ 2 + 0 * t ^ 3) * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, d1, deriv_cubic]; funext t; ring
  have d3 : iteratedDeriv 3 (mgf id (gaussianReal 0 1)) =
      fun t ↦ (0 + 3 * t + 0 * t ^ 2 + 1 * t ^ 3) * Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, d2, deriv_cubic]; funext t; ring
  have d4 : iteratedDeriv 4 (mgf id (gaussianReal 0 1)) =
      fun t ↦ (3 + 0 * t + 3 * 1 * t ^ 2 + t * (0 + 3 * t + 0 * t ^ 2 + 1 * t ^ 3)) *
        Real.exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, d3, deriv_cubic]; funext t; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [d1]; simp
  · rw [d2]; simp
  · rw [d3]; simp
  · rw [d4]; norm_num

lemma zero_mem_int : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
  simp

lemma integrable_pow_N01 (n : ℕ) : Integrable (fun x : ℝ ↦ x ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet zero_mem_int n

lemma moment_N01 (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 1) = iteratedDeriv n (mgf id (gaussianReal 0 1)) 0 := by
  rw [iteratedDeriv_mgf_zero zero_mem_int n]; rfl

/-- Integral of a degree-4 polynomial against `N(0,1)`. -/
lemma integral_poly (c0 c1 c2 c3 c4 : ℝ) :
    Integrable (fun x : ℝ ↦ c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4)
        (gaussianReal 0 1) ∧
    ∫ x, (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4) ∂(gaussianReal 0 1) =
      c0 + c2 + 3 * c4 := by
  have i1 := (integrable_pow_N01 1).const_mul c1
  have i2 := (integrable_pow_N01 2).const_mul c2
  have i3 := (integrable_pow_N01 3).const_mul c3
  have i4 := (integrable_pow_N01 4).const_mul c4
  have i0 : Integrable (fun _ : ℝ ↦ c0) (gaussianReal 0 1) := integrable_const _
  simp only [pow_one] at i1
  refine ⟨(((i0.add i1).add i2).add i3).add i4, ?_⟩
  rw [integral_add (f := fun x : ℝ ↦ c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3)
      (g := fun x : ℝ ↦ c4 * x ^ 4) (((i0.add i1).add i2).add i3) i4,
    integral_add (f := fun x : ℝ ↦ c0 + c1 * x + c2 * x ^ 2)
      (g := fun x : ℝ ↦ c3 * x ^ 3) ((i0.add i1).add i2) i3,
    integral_add (f := fun x : ℝ ↦ c0 + c1 * x)
      (g := fun x : ℝ ↦ c2 * x ^ 2) (i0.add i1) i2,
    integral_add (f := fun _ : ℝ ↦ c0) (g := fun x : ℝ ↦ c1 * x) i0 i1]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    moment_N01 2, moment_N01 3, moment_N01 4]
  have m1 := moment_N01 1
  simp only [pow_one] at m1
  rw [m1]
  obtain ⟨h1, h2, h3, h4⟩ := iter_mgf
  rw [h1, h2, h3, h4]
  simp only [probReal_univ, smul_eq_mul, integral_const]
  ring

/-! ### One coordinate of the energy statistic -/

lemma coord_int (a m : ℝ) :
    Integrable (fun g : ℝ ↦ (a + m * g) ^ 2) (gaussianReal 0 1) ∧
    ∫ g, (a + m * g) ^ 2 ∂(gaussianReal 0 1) = a ^ 2 + m ^ 2 := by
  have h := integral_poly (a ^ 2) (2 * a * m) (m ^ 2) 0 0
  have e : (fun g : ℝ ↦ (a + m * g) ^ 2) =
      fun x ↦ a ^ 2 + 2 * a * m * x + m ^ 2 * x ^ 2 + 0 * x ^ 3 + 0 * x ^ 4 := by
    funext x; ring
  rw [e]; exact ⟨h.1, by rw [h.2]; ring⟩

lemma coord_sq_int (a m : ℝ) :
    Integrable (fun g : ℝ ↦ ((a + m * g) ^ 2) ^ 2) (gaussianReal 0 1) ∧
    ∫ g, ((a + m * g) ^ 2) ^ 2 ∂(gaussianReal 0 1) = a ^ 4 + 6 * a ^ 2 * m ^ 2 + 3 * m ^ 4 := by
  have h := integral_poly (a ^ 4) (4 * a ^ 3 * m) (6 * a ^ 2 * m ^ 2) (4 * a * m ^ 3) (m ^ 4)
  have e : (fun g : ℝ ↦ ((a + m * g) ^ 2) ^ 2) =
      fun x ↦ a ^ 4 + 4 * a ^ 3 * m * x + 6 * a ^ 2 * m ^ 2 * x ^ 2 + 4 * a * m ^ 3 * x ^ 3 +
        m ^ 4 * x ^ 4 := by
    funext x; ring
  rw [e]; exact ⟨h.1, h.2⟩

lemma coord_memLp (a m : ℝ) : MemLp (fun g : ℝ ↦ (a + m * g) ^ 2) 2 (gaussianReal 0 1) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).2 (coord_sq_int a m).1

lemma coord_var (a m : ℝ) :
    Var[fun g : ℝ ↦ (a + m * g) ^ 2; gaussianReal 0 1] = 4 * a ^ 2 * m ^ 2 + 2 * m ^ 4 := by
  rw [variance_eq_sub (coord_memLp a m)]
  have h1 := (coord_int a m).2
  have h2 := (coord_sq_int a m).2
  simp only [Pi.pow_apply] at *
  rw [h1, h2]; ring

/-! ### The energy statistic under the product measure -/

/-- `Q(x) = Σ_i (t_i + m_i x_i)²`. -/
noncomputable def Qs {D : ℕ} (t m : Fin D → ℝ) (x : Fin D → ℝ) : ℝ :=
  ∑ i, (t i + m i * x i) ^ 2

lemma Qs_eq_sum {D : ℕ} (t m : Fin D → ℝ) :
    Qs t m = ∑ i, fun x : Fin D → ℝ ↦ (fun g : ℝ ↦ (t i + m i * g) ^ 2) (x i) := by
  funext x; simp [Qs, Finset.sum_apply]

lemma Qs_memLp {D : ℕ} (t m : Fin D → ℝ) : MemLp (Qs t m) 2 (piN D) := by
  rw [Qs_eq_sum]
  exact memLp_finsetSum' _ fun i _ ↦
    (coord_memLp (t i) (m i)).comp_measurePreserving (measurePreserving_eval _ i)

lemma Qs_mean {D : ℕ} (t m : Fin D → ℝ) :
    ∫ x, Qs t m x ∂(piN D) = ∑ i, (t i ^ 2 + m i ^ 2) := by
  unfold Qs
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_comp_eval (μ := fun _ : Fin D ↦ gaussianReal 0 1)
      (f := fun g : ℝ ↦ (t i + m i * g) ^ 2) (by fun_prop)]
    exact (coord_int (t i) (m i)).2
  · intro i _
    exact ((coord_memLp (t i) (m i)).comp_measurePreserving
      (measurePreserving_eval _ i)).integrable one_le_two

lemma Qs_var {D : ℕ} (t m : Fin D → ℝ) :
    Var[Qs t m; piN D] = ∑ i, (4 * t i ^ 2 * m i ^ 2 + 2 * m i ^ 4) := by
  rw [Qs_eq_sum, variance_sum_pi (fun i ↦ coord_memLp (t i) (m i))]
  exact Finset.sum_congr rfl fun i _ ↦ coord_var (t i) (m i)

/-- Chebyshev for `Q`. -/
lemma Qs_cheb {D : ℕ} (t m : Fin D → ℝ) (c : ℝ) (hc : 0 < c) (s : Set (Fin D → ℝ))
    (hs : ∀ x ∈ s, c ≤ |Qs t m x - ∑ i, (t i ^ 2 + m i ^ 2)|) :
    (piN D).real s ≤ (∑ i, (4 * t i ^ 2 * m i ^ 2 + 2 * m i ^ 4)) / c ^ 2 := by
  have h := meas_ge_le_variance_div_sq (Qs_memLp t m) hc
  rw [Qs_var, Qs_mean] at h
  have hsub : s ⊆ {ω | c ≤ |Qs t m ω - ∑ i, (t i ^ 2 + m i ^ 2)|} := fun x hx ↦ hs x hx
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((measure_mono hsub).trans h)

end HigherOrderId.Certify.Dev.C1
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.C1
open HigherOrderId.Certify

lemma frob_sq {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef) :
    frobNorm S ^ 2 = ∑ i, mu S i ^ 4 := by
  rw [frobNorm, Real.sq_sqrt, frob_eq S hS]
  rw [frob_eq S hS]; positivity

lemma frob_nonneg {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) : 0 ≤ frobNorm S := Real.sqrt_nonneg _

lemma mu_sq_le {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef) (i : Fin D) :
    mu S i ^ 2 ≤ frobNorm S := by
  rw [frobNorm, frob_eq S hS]
  apply Real.le_sqrt_of_sq_le
  have := Finset.single_le_sum (f := fun j ↦ mu S j ^ 4) (fun j _ ↦ by positivity)
    (Finset.mem_univ i)
  simpa [← pow_mul] using this

lemma norm_sq_coord {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (θ : EuclideanSpace ℝ (Fin D)) :
    ‖θ‖ ^ 2 = ∑ i, (inner ℝ (bas S i) θ) ^ 2 := by
  conv_lhs => rw [← V_coord S θ]
  exact norm_V_sq S _

lemma measurable_energyRule {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (ε : ℝ) :
    Measurable (energyRule S ε) := by
  unfold energyRule
  refine Measurable.indicator measurable_const ?_
  exact measurableSet_le (by fun_prop) measurable_const

lemma energy_integral {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef) (ε : ℝ)
    (θ : EuclideanSpace ℝ (Fin D)) :
    ∫ x, energyRule S ε x ∂(multivariateGaussian θ S) =
      (piN D).real {x | Qs (fun i ↦ inner ℝ (bas S i) θ) (mu S) x - ∑ i, mu S i ^ 2 ≤ ε / 2} := by
  rw [integral_mvg S θ _ (measurable_energyRule S ε)]
  have hm : MeasurableSet
      {x : Fin D → ℝ | Qs (fun i ↦ inner ℝ (bas S i) θ) (mu S) x - ∑ i, mu S i ^ 2 ≤ ε / 2} := by
    refine measurableSet_le ?_ measurable_const
    unfold Qs; fun_prop
  rw [← integral_indicator_one hm]
  congr 1
  funext x
  simp only [energyRule, Set.indicator_apply, Set.mem_ofPred_eq, norm_V_sq, trace_eq S hS, Qs,
    Pi.one_apply]

lemma part2 (D : ℕ) (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef)
    (δ β R ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β)
    (hε0 : 0 < ε) (hC : CUpper δ β * frobNorm S ≤ ε) :
    IsSafe S R ε δ (energyRule S ε) ∧ 1 - β ≤ nullPower S (energyRule S ε) := by
  have hF0 := frob_nonneg S
  have hF2 := frob_sq S hS
  set F := frobNorm S with hFdef
  have hC1 : 32 / δ * F ≤ ε :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hF0).trans hC
  have hC2 : Real.sqrt (8 / β) * F ≤ ε :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hF0).trans hC
  have hFd : 32 * F ≤ δ * ε := by
    have := mul_le_mul_of_nonneg_left hC1 hδ0.le
    rw [← mul_assoc, mul_div_cancel₀ _ hδ0.ne'] at this
    exact this
  have hvar : ∀ t : Fin D → ℝ,
      ∑ i, (4 * t i ^ 2 * mu S i ^ 2 + 2 * mu S i ^ 4) ≤ 4 * F * ∑ i, t i ^ 2 + 2 * F ^ 2 := by
    intro t
    rw [hF2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have := mu_sq_le S hS i
    have ht : 0 ≤ t i ^ 2 := sq_nonneg _
    nlinarith
  refine ⟨?_, ?_⟩
  · intro θ hθ1 _
    rw [energy_integral S hS ε θ]
    set t : Fin D → ℝ := fun i ↦ inner ℝ (bas S i) θ with ht
    have hT : ‖θ‖ ^ 2 = ∑ i, t i ^ 2 := norm_sq_coord S θ
    set T := ∑ i, t i ^ 2 with hTdef
    have hTpos : 0 < T := by rw [← hT]; linarith
    have hc := Qs_cheb t (mu S) (T / 2) (by positivity)
      {x | Qs t (mu S) x - ∑ i, mu S i ^ 2 ≤ ε / 2} (fun x hx ↦ by
        simp only [Set.mem_ofPred_eq] at hx
        rw [Finset.sum_add_distrib, ← hTdef]
        rw [abs_sub_comm, le_abs]; left; linarith)
    refine hc.trans ?_
    rw [div_le_iff₀ (by positivity)]
    refine (hvar t).trans ?_
    have h1 : 32 * F ≤ δ * T := hFd.trans (by nlinarith)
    nlinarith
  · unfold nullPower
    rw [energy_integral S hS ε 0]
    simp only [inner_zero_right]
    have hm : MeasurableSet
        {x : Fin D → ℝ | Qs (fun _ ↦ 0) (mu S) x - ∑ i, mu S i ^ 2 ≤ ε / 2} := by
      refine measurableSet_le ?_ measurable_const
      unfold Qs; fun_prop
    have hc := Qs_cheb (fun _ ↦ 0) (mu S) (ε / 2) (by positivity)
      {x | Qs (fun _ ↦ 0) (mu S) x - ∑ i, mu S i ^ 2 ≤ ε / 2}ᶜ (fun x hx ↦ by
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
        rw [le_abs]; left; linarith)
    rw [probReal_compl_eq_one_sub hm] at hc
    have hv := hvar (fun _ ↦ 0)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      mul_zero, zero_add, zero_mul] at hv
    have hsq : 8 * F ^ 2 ≤ β * ε ^ 2 := by
      have h0 : 0 ≤ Real.sqrt (8 / β) * F := by positivity
      have := mul_self_le_mul_self h0 hC2
      have e : Real.sqrt (8 / β) * F * (Real.sqrt (8 / β) * F) = 8 / β * F ^ 2 := by
        rw [show Real.sqrt (8 / β) * F * (Real.sqrt (8 / β) * F) =
          (Real.sqrt (8 / β)) ^ 2 * F ^ 2 by ring, Real.sq_sqrt (by positivity)]
      rw [e] at this
      have := mul_le_mul_of_nonneg_left this hβ0.le
      rw [← mul_assoc, mul_div_cancel₀ _ hβ0.ne'] at this
      nlinarith
    have hq : (∑ i, (4 * (fun _ ↦ (0 : ℝ)) i ^ 2 * mu S i ^ 2 + 2 * mu S i ^ 4)) / (ε / 2) ^ 2
        ≤ β := by
      rw [div_le_iff₀ (by positivity)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_mul, zero_add]
      nlinarith
    linarith [hc.trans hq]

end HigherOrderId.Certify.Dev.C1
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory

namespace HigherOrderId.Certify.Dev.C1
open HigherOrderId.Certify

/-! ### Cameron–Martin for the standard Gaussian product -/

/-- Likelihood ratio of `N(a,1)` against `N(0,1)`. -/
noncomputable def lr (a y : ℝ) : ℝ := Real.exp (a * y - a ^ 2 / 2)

lemma lr_pos (a y : ℝ) : 0 < lr a y := Real.exp_pos _

@[fun_prop] lemma measurable_lr (a : ℝ) : Measurable (fun y ↦ lr a y) := by unfold lr; fun_prop

lemma integral_exp_N01 (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simp only [mgf, id] at this
  rw [this]; congr 1; simp

lemma integrable_exp_N01 (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * x)) (gaussianReal 0 1) :=
  integrable_exp_mul_gaussianReal t

lemma lr_eq (a y : ℝ) : lr a y = Real.exp (-(a ^ 2 / 2)) * Real.exp (a * y) := by
  rw [lr, ← Real.exp_add]; ring_nf

lemma integrable_lr (a : ℝ) : Integrable (lr a) (gaussianReal 0 1) := by
  have := (integrable_exp_N01 a).const_mul (Real.exp (-(a ^ 2 / 2)))
  simpa only [← lr_eq] using this

lemma cm1 (a : ℝ) :
    gaussianReal a 1 = (gaussianReal 0 1).withDensity (fun y ↦ ENNReal.ofReal (lr a y)) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext y
  simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal, lr]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- Product likelihood ratio. -/
noncomputable def plr {D : ℕ} (a : Fin D → ℝ) (x : Fin D → ℝ) : ℝ := ∏ i, lr (a i) (x i)

lemma plr_nonneg {D : ℕ} (a x : Fin D → ℝ) : 0 ≤ plr a x :=
  Finset.prod_nonneg fun _ _ ↦ (lr_pos _ _).le

@[fun_prop] lemma measurable_plr {D : ℕ} (a : Fin D → ℝ) : Measurable (fun x ↦ plr a x) := by
  unfold plr; fun_prop

lemma cm_pi {D : ℕ} (a : Fin D → ℝ) :
    Measure.pi (fun i ↦ gaussianReal (a i) 1) =
      (piN D).withDensity (fun x ↦ ENNReal.ofReal (plr a x)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator
    (MeasurableSet.univ_pi hs)]
  have hfun : (Set.univ.pi s).indicator (fun x ↦ ENNReal.ofReal (plr a x)) =
      fun x ↦ ENNReal.ofReal (∏ i, (s i).indicator (lr (a i)) (x i)) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx, plr]
      congr 1
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  have hint : ∀ i, Integrable ((s i).indicator (lr (a i))) (gaussianReal 0 1) :=
    fun i ↦ (integrable_lr (a i)).indicator (hs i)
  have hnn : ∀ i y, 0 ≤ (s i).indicator (lr (a i)) y :=
    fun i y ↦ Set.indicator_nonneg (fun _ _ ↦ (lr_pos _ _).le) y
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hint)
      (ae_of_all _ fun x ↦ Finset.prod_nonneg fun i _ ↦ hnn i _),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ ↦ integral_nonneg (hnn i))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [cm1 (a i), withDensity_apply _ (hs i), ← lintegral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hint i) (ae_of_all _ (hnn i))]
  congr 1
  funext y
  by_cases hy : y ∈ s i
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

lemma shift_pi {D : ℕ} (a : Fin D → ℝ) :
    (piN D).map (fun x i ↦ x i + a i) = Measure.pi (fun i ↦ gaussianReal (a i) 1) := by
  have : ∀ i, SigmaFinite ((gaussianReal 0 1).map (· + a i)) := by
    intro i; rw [gaussianReal_map_add_const]; infer_instance
  rw [Measure.pi_map_pi (f := fun i (y : ℝ) ↦ y + a i) (fun i ↦ by fun_prop)]
  congr 1; funext i
  rw [gaussianReal_map_add_const, zero_add]

/-- Cameron–Martin: `∫ ψ(x + a) dN(0,I) = ∫ ψ(x) Π_i e^{a_i x_i − a_i²/2} dN(0,I)`. -/
lemma integral_shift {D : ℕ} (a : Fin D → ℝ) (ψ : (Fin D → ℝ) → ℝ) (hψ : Measurable ψ) :
    ∫ x, ψ (fun i ↦ x i + a i) ∂(piN D) = ∫ x, plr a x * ψ x ∂(piN D) := by
  rw [← integral_map (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).add_const _).aemeasurable
    hψ.aestronglyMeasurable, shift_pi, cm_pi]
  have := integral_withDensity_eq_integral_smul (μ := piN D)
    (f := fun x ↦ (plr a x).toNNReal) (by fun_prop) ψ
  refine this.trans ?_
  congr 1; funext x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (plr_nonneg a x)]

end HigherOrderId.Certify.Dev.C1
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory

namespace HigherOrderId.Certify.Dev.C1
open HigherOrderId.Certify

/-! ### The χ² bound for the sign mixture -/

/-- Sign of a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- One-coordinate mixture density `(e^{hy} + e^{-hy}) e^{-h²/2} / 2`. -/
noncomputable def cc (h y : ℝ) : ℝ := (lr h y + lr (-h) y) / 2

/-- Product mixture density. -/
noncomputable def mix {D : ℕ} (h : Fin D → ℝ) (x : Fin D → ℝ) : ℝ := ∏ i, cc (h i) (x i)

@[fun_prop] lemma measurable_cc (h : ℝ) : Measurable (fun y ↦ cc h y) := by
  unfold cc; fun_prop

@[fun_prop] lemma measurable_mix {D : ℕ} (h : Fin D → ℝ) : Measurable (fun x ↦ mix h x) := by
  unfold mix; fun_prop

lemma sum_plr {D : ℕ} (h x : Fin D → ℝ) :
    ∑ s : Fin D → Bool, plr (fun i ↦ sgn (s i) * h i) x = 2 ^ D * mix h x := by
  unfold plr mix
  rw [← Fintype.prod_sum (fun i (b : Bool) ↦ lr (sgn b * h i) (x i))]
  have : ∀ i, ∑ b : Bool, lr (sgn b * h i) (x i) = 2 * cc (h i) (x i) := by
    intro i
    simp [sgn, cc]
    ring
  simp_rw [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma integrable_cc (h : ℝ) : Integrable (fun y ↦ cc h y) (gaussianReal 0 1) := by
  unfold cc
  exact ((integrable_lr h).add (integrable_lr (-h))).div_const 2

lemma integral_cc (h : ℝ) : ∫ y, cc h y ∂(gaussianReal 0 1) = 1 := by
  unfold cc
  rw [integral_div, integral_add (integrable_lr h) (integrable_lr (-h))]
  simp only [lr_eq]
  rw [integral_const_mul, integral_const_mul, integral_exp_N01, integral_exp_N01,
    ← Real.exp_add, ← Real.exp_add]
  have e1 : -(h ^ 2 / 2) + h ^ 2 / 2 = 0 := by ring
  have e2 : -((-h) ^ 2 / 2) + (-h) ^ 2 / 2 = 0 := by ring
  rw [e1, e2]; simp

lemma cc_sq (h y : ℝ) :
    cc h y ^ 2 = (Real.exp (-h ^ 2) * Real.exp (2 * h * y) + 2 * Real.exp (-h ^ 2) +
      Real.exp (-h ^ 2) * Real.exp (-(2 * h) * y)) / 4 := by
  have hE : Real.exp (-(h ^ 2 / 2)) ^ 2 = Real.exp (-h ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hA : Real.exp (h * y) ^ 2 = Real.exp (2 * h * y) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hB : Real.exp (-h * y) ^ 2 = Real.exp (-(2 * h) * y) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hAB : Real.exp (h * y) * Real.exp (-h * y) = 1 := by
    rw [← Real.exp_add]; simp
  have hE2 : Real.exp (-((-h) ^ 2 / 2)) = Real.exp (-(h ^ 2 / 2)) := by congr 1; ring
  unfold cc
  rw [lr_eq, lr_eq, hE2, ← hE, ← hA, ← hB]
  linear_combination (Real.exp (-(h ^ 2 / 2)) ^ 2 / 2) * hAB

lemma integrable_cc_sq (h : ℝ) : Integrable (fun y ↦ cc h y ^ 2) (gaussianReal 0 1) := by
  simp_rw [cc_sq]
  exact ((((integrable_exp_N01 (2 * h)).const_mul _).add (integrable_const _)).add
    ((integrable_exp_N01 (-(2 * h))).const_mul _)).div_const 4

lemma integral_cc_sq (h : ℝ) : ∫ y, cc h y ^ 2 ∂(gaussianReal 0 1) = Real.cosh (h ^ 2) := by
  simp_rw [cc_sq]
  rw [integral_div, integral_add
      (f := fun y ↦ Real.exp (-h ^ 2) * Real.exp (2 * h * y) + 2 * Real.exp (-h ^ 2))
      (g := fun y ↦ Real.exp (-h ^ 2) * Real.exp (-(2 * h) * y))
      (((integrable_exp_N01 (2 * h)).const_mul _).add
      (integrable_const _)) ((integrable_exp_N01 (-(2 * h))).const_mul _),
    integral_add (f := fun y ↦ Real.exp (-h ^ 2) * Real.exp (2 * h * y))
      (g := fun _ ↦ 2 * Real.exp (-h ^ 2))
      ((integrable_exp_N01 (2 * h)).const_mul _) (integrable_const _),
    integral_const_mul, integral_exp_N01, integral_const, integral_const_mul, integral_exp_N01]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [← Real.exp_add, ← Real.exp_add, Real.cosh_eq]
  have e1 : -h ^ 2 + (2 * h) ^ 2 / 2 = h ^ 2 := by ring
  have e2 : -h ^ 2 + (-(2 * h)) ^ 2 / 2 = h ^ 2 := by ring
  rw [e1, e2]
  have : Real.exp (-h ^ 2) = Real.exp (-(h ^ 2)) := by ring_nf
  rw [this]; ring

lemma integrable_mix {D : ℕ} (h : Fin D → ℝ) : Integrable (mix h) (piN D) :=
  Integrable.fintype_prod (f := fun i y ↦ cc (h i) y) fun i ↦ integrable_cc (h i)

lemma integral_mix {D : ℕ} (h : Fin D → ℝ) : ∫ x, mix h x ∂(piN D) = 1 := by
  unfold mix
  rw [integral_fintype_prod_eq_prod (f := fun i y ↦ cc (h i) y)]
  simp [integral_cc]

lemma mix_sq {D : ℕ} (h : Fin D → ℝ) (x : Fin D → ℝ) :
    mix h x ^ 2 = ∏ i, cc (h i) (x i) ^ 2 := by
  unfold mix; rw [Finset.prod_pow]

lemma integrable_mix_sq {D : ℕ} (h : Fin D → ℝ) :
    Integrable (fun x ↦ mix h x ^ 2) (piN D) := by
  simp_rw [mix_sq]
  exact Integrable.fintype_prod (f := fun i y ↦ cc (h i) y ^ 2) fun i ↦ integrable_cc_sq (h i)

lemma integral_mix_sq_le {D : ℕ} (h : Fin D → ℝ) :
    ∫ x, mix h x ^ 2 ∂(piN D) ≤ Real.exp ((∑ i, h i ^ 4) / 2) := by
  simp_rw [mix_sq]
  rw [integral_fintype_prod_eq_prod (f := fun i y ↦ cc (h i) y ^ 2)]
  simp_rw [integral_cc_sq]
  rw [Finset.sum_div, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ ↦ (Real.cosh_pos _).le) fun i _ ↦ ?_
  have := Real.cosh_le_exp_half_sq (h i ^ 2)
  rw [← pow_mul] at this
  exact this

/-- Pointwise inequality behind the χ² bound. -/
lemma pt_ineq (p m K : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hK : 0 < K) :
    p * (1 - m) ≤ (K / 2 + 1 / (8 * K) + 1 / 2) + (-(2 / (8 * K)) - 1 / 2) * m +
      (1 / (8 * K)) * m ^ 2 := by
  have key : 8 * K * (p * (1 - m)) ≤
      8 * K * ((K / 2 + 1 / (8 * K) + 1 / 2) + (-(2 / (8 * K)) - 1 / 2) * m +
        (1 / (8 * K)) * m ^ 2) := by
    have e : 8 * K * ((K / 2 + 1 / (8 * K) + 1 / 2) + (-(2 / (8 * K)) - 1 / 2) * m +
        (1 / (8 * K)) * m ^ 2) = 4 * K ^ 2 + (1 - m) ^ 2 + 4 * K * (1 - m) := by
      field_simp; ring
    rw [e]
    nlinarith [sq_nonneg ((1 - m) - 4 * K * (p - 1 / 2)), mul_nonneg hp0 (sub_nonneg.2 hp1),
      mul_pos hK hK]
  exact le_of_mul_le_mul_left key (by positivity)

lemma chi2 {D : ℕ} (h : Fin D → ℝ) (ψ : (Fin D → ℝ) → ℝ) (hψm : Measurable ψ)
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (δ β : ℝ) (hK : 0 < 1 - δ - β)
    (hnull : 1 - β ≤ ∫ x, ψ x ∂(piN D))
    (halt : ∀ s : Fin D → Bool, ∫ x, ψ (fun i ↦ x i + sgn (s i) * h i) ∂(piN D) ≤ δ) :
    4 * (1 - δ - β) ^ 2 ≤ Real.exp ((∑ i, h i ^ 4) / 2) - 1 := by
  set K := 1 - δ - β with hKdef
  have hbd : ∀ x, ‖ψ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hψ x]
  have hψi : Integrable ψ (piN D) :=
    (integrable_const (1 : ℝ)).bdd_mul hψm.aestronglyMeasurable (ae_of_all _ hbd) |>.congr
      (ae_of_all _ fun x ↦ by simp)
  have hψM : Integrable (fun x ↦ ψ x * mix h x) (piN D) :=
    (integrable_mix h).bdd_mul hψm.aestronglyMeasurable (ae_of_all _ hbd)
  -- the mixture is rejected with probability at most δ
  have hmixδ : ∫ x, ψ x * mix h x ∂(piN D) ≤ δ := by
    have hplr : ∀ s : Fin D → Bool,
        ∫ x, plr (fun i ↦ sgn (s i) * h i) x * ψ x ∂(piN D) ≤ δ := by
      intro s
      rw [← integral_shift _ ψ hψm]; exact halt s
    have hint : ∀ s : Fin D → Bool,
        Integrable (fun x ↦ plr (fun i ↦ sgn (s i) * h i) x * ψ x) (piN D) := by
      intro s
      have hp : Integrable (plr (fun i ↦ sgn (s i) * h i)) (piN D) :=
        Integrable.fintype_prod (f := fun i y ↦ lr (sgn (s i) * h i) y)
          fun i ↦ integrable_lr _
      have := hp.bdd_mul hψm.aestronglyMeasurable (ae_of_all _ hbd)
      refine this.congr (ae_of_all _ fun x ↦ ?_)
      simp only; ring
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun s _ ↦ hplr s
    rw [← integral_finsetSum _ fun s _ ↦ hint s] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have e : (fun x ↦ ∑ s : Fin D → Bool, plr (fun i ↦ sgn (s i) * h i) x * ψ x) =
        fun x ↦ (2 : ℝ) ^ D * (ψ x * mix h x) := by
      funext x; rw [← Finset.sum_mul, sum_plr]; ring
    rw [e, integral_const_mul] at hsum
    push_cast at hsum
    exact le_of_mul_le_mul_left hsum (by positivity)
  -- integrate the pointwise inequality
  have hM := integrable_mix h
  have hM2 := integrable_mix_sq h
  have hR : Integrable (fun x ↦ (K / 2 + 1 / (8 * K) + 1 / 2) +
      (-(2 / (8 * K)) - 1 / 2) * mix h x + (1 / (8 * K)) * mix h x ^ 2) (piN D) :=
    ((integrable_const _).add (hM.const_mul _)).add (hM2.const_mul _)
  have hL : Integrable (fun x ↦ ψ x * (1 - mix h x)) (piN D) := by
    have := hψi.sub hψM
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.sub_apply]; ring
  have hmono := integral_mono hL hR fun x ↦ pt_ineq (ψ x) (mix h x) K (hψ x).1 (hψ x).2 hK
  have hLval : ∫ x, ψ x * (1 - mix h x) ∂(piN D) =
      ∫ x, ψ x ∂(piN D) - ∫ x, ψ x * mix h x ∂(piN D) := by
    rw [← integral_sub hψi hψM]; congr 1; funext x; ring
  have hRval : ∫ x, ((K / 2 + 1 / (8 * K) + 1 / 2) +
      (-(2 / (8 * K)) - 1 / 2) * mix h x + (1 / (8 * K)) * mix h x ^ 2) ∂(piN D) =
      (K / 2 + 1 / (8 * K) + 1 / 2) + (-(2 / (8 * K)) - 1 / 2) * 1 +
        (1 / (8 * K)) * ∫ x, mix h x ^ 2 ∂(piN D) := by
    rw [integral_add (f := fun x ↦ (K / 2 + 1 / (8 * K) + 1 / 2) +
        (-(2 / (8 * K)) - 1 / 2) * mix h x) (g := fun x ↦ (1 / (8 * K)) * mix h x ^ 2)
        ((integrable_const _).add (hM.const_mul _)) (hM2.const_mul _),
      integral_add (f := fun _ ↦ (K / 2 + 1 / (8 * K) + 1 / 2))
        (g := fun x ↦ (-(2 / (8 * K)) - 1 / 2) * mix h x)
        (integrable_const _) (hM.const_mul _), integral_const, integral_const_mul,
      integral_const_mul, integral_mix]
    simp
  rw [hLval, hRval] at hmono
  have hsq := integral_mix_sq_le h
  have h8 : K ≤ K / 2 + (1 / (8 * K)) * (∫ x, mix h x ^ 2 ∂(piN D) - 1) := by
    have : (K / 2 + 1 / (8 * K) + 1 / 2) + (-(2 / (8 * K)) - 1 / 2) * 1 +
        (1 / (8 * K)) * ∫ x, mix h x ^ 2 ∂(piN D) =
        K / 2 + (1 / (8 * K)) * (∫ x, mix h x ^ 2 ∂(piN D) - 1) := by ring
    linarith
  have h9 : 4 * K ^ 2 ≤ ∫ x, mix h x ^ 2 ∂(piN D) - 1 := by
    have h10 : K / 2 ≤ (1 / (8 * K)) * (∫ x, mix h x ^ 2 ∂(piN D) - 1) := by linarith
    have h11 := mul_le_mul_of_nonneg_left h10 (by positivity : (0 : ℝ) ≤ 8 * K)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at h11
    nlinarith
  linarith

end HigherOrderId.Certify.Dev.C1
end

section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.C1
open HigherOrderId.Certify

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

lemma part1 (D : ℕ) (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosSemidef)
    (δ β R ε : ℝ) (hδ1 : δ < 1 / 4) (hβ1 : β < 1 / 4)
    (hε0 : 0 < ε) (hεR : ε ≤ R ^ 2)
    (φ : EuclideanSpace ℝ (Fin D) → ℝ) (hφ : IsRandomizedRule φ) (hsafe : IsSafe S R ε δ φ)
    (hnull : 1 - β ≤ nullPower S φ) : cLower δ β * frobNorm S ≤ ε := by
  have hF0 := frob_nonneg S
  have hF2 := frob_sq S hS
  set F := frobNorm S with hFdef
  rcases hF0.eq_or_lt with hF | hF
  · rw [← hF, mul_zero]; exact hε0.le
  set h : Fin D → ℝ := fun i ↦ mu S i * Real.sqrt ε / F with hh
  set ψ : (Fin D → ℝ) → ℝ := fun x ↦ φ (V S (fun i ↦ mu S i * x i)) with hψdef
  have hψm : Measurable ψ := hφ.1.comp ((measurable_V S).comp (by fun_prop))
  have hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1 := fun x ↦ hφ.2 _
  have hK : 0 < 1 - δ - β := by linarith
  have hsε : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0.le
  have hnull' : 1 - β ≤ ∫ x, ψ x ∂(piN D) := by
    refine hnull.trans (le_of_eq ?_)
    rw [nullPower, integral_mvg S 0 φ hφ.1]
    simp [hψdef]
  have halt : ∀ s : Fin D → Bool,
      ∫ x, ψ (fun i ↦ x i + sgn (s i) * h i) ∂(piN D) ≤ δ := by
    intro s
    set θ := V S (fun i ↦ sgn (s i) * mu S i * h i) with hθ
    have hnorm : ‖θ‖ ^ 2 = ε := by
      rw [hθ, norm_V_sq]
      have : ∀ i, (sgn (s i) * mu S i * h i) ^ 2 = ε / F ^ 2 * mu S i ^ 4 := by
        intro i
        rw [hh]; simp only
        rw [mul_pow, mul_pow, sgn_sq, div_pow, mul_pow, hsε]
        field_simp
      simp_rw [this]
      rw [← Finset.mul_sum, ← hF2]
      field_simp
    have := hsafe θ hnorm.ge (hnorm.symm ▸ hεR)
    rw [integral_mvg S θ φ hφ.1] at this
    refine le_of_eq_of_le ?_ this
    congr 1; funext x
    simp only [hψdef, hθ, inner_V]
    congr 2; funext i; ring
  have hchi := chi2 h ψ hψm hψ δ β hK hnull' halt
  have hsum : ∑ i, h i ^ 4 = ε ^ 2 / F ^ 2 := by
    have : ∀ i, h i ^ 4 = (ε ^ 2 / F ^ 4) * mu S i ^ 4 := by
      intro i
      rw [hh]; simp only
      rw [div_pow, mul_pow, show Real.sqrt ε ^ 4 = (Real.sqrt ε ^ 2) ^ 2 by ring, hsε]
      field_simp
    simp_rw [this]
    rw [← Finset.mul_sum, ← hF2]
    field_simp
  rw [hsum] at hchi
  -- conclude
  have hlog : Real.log (1 + 4 * (1 - δ - β) ^ 2) ≤ ε ^ 2 / F ^ 2 / 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    linarith
  have hc : cLower δ β ≤ ε / F := by
    unfold cLower
    rw [show ε / F = Real.sqrt ((ε / F) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_pow]; linarith
  have := mul_le_mul_of_nonneg_right hc hF.le
  rwa [div_mul_cancel₀ _ hF.ne'] at this

end HigherOrderId.Certify.Dev.C1

namespace HigherOrderId.Certify
open HigherOrderId.Certify.Dev.C1 in
theorem chk_lemma_C_1 (D : ℕ) (S : Matrix (Fin D) (Fin D) ℝ) (hS : S.PosDef)
    (δ β R ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hβ0 : 0 < β) (hβ1 : β < 1 / 4)
    (hε0 : 0 < ε) (hεR : ε ≤ R ^ 2) :
    (∀ φ : EuclideanSpace ℝ (Fin D) → ℝ, IsRandomizedRule φ → IsSafe S R ε δ φ →
        1 - β ≤ nullPower S φ → cLower δ β * frobNorm S ≤ ε) ∧
    (CUpper δ β * frobNorm S ≤ ε →
        IsSafe S R ε δ (energyRule S ε) ∧ 1 - β ≤ nullPower S (energyRule S ε)) :=
  ⟨fun φ hφ hsafe hnull ↦
      part1 D S hS.posSemidef δ β R ε hδ1 hβ1 hε0 hεR φ hφ hsafe hnull,
    fun hC ↦ part2 D S hS.posSemidef δ β R ε hδ0 hδ1 hβ0 hε0 hC⟩

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_lemma_C_1 := @HigherOrderId.Certify.chk_lemma_C_1
