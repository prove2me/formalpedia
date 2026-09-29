-- Prove2me | solution 1 for LesHouchesWidth.covariance_first_layer
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:01:17.015959+00:00
-- url     : https://prove2.me/submissions/c6545a6e-3562-4685-b8b9-cc2726636448

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth
import Definitions.Def_LesHouchesWidth_ReLUNet

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LesHouchesWidth

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W5_LesHouchesWidth_gfacts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {v : ℝ≥0} (h : P.map f = gaussianReal 0 v) :
    AEMeasurable f P ∧ MemLp f 2 P ∧ ∫ ω, f ω ∂P = 0 ∧ ∫ ω, f ω * f ω ∂P = v := by
  have hf : AEMeasurable f P := by
    by_contra hc
    rw [Measure.map_of_not_aemeasurable hc] at h
    have h2 : (0 : Measure ℝ) Set.univ = gaussianReal 0 v Set.univ := by rw [h]
    simp at h2
  have hmem : MemLp f 2 P := by
    have h3 := memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)
    rw [← h] at h3
    exact (memLp_map_measure_iff aestronglyMeasurable_id hf).1 h3
  have hint : ∫ ω, f ω ∂P = 0 := by
    calc ∫ ω, f ω ∂P = ∫ y, y ∂(P.map f) := (integral_map hf aestronglyMeasurable_id).symm
      _ = 0 := by rw [h, integral_id_gaussianReal]
  refine ⟨hf, hmem, hint, ?_⟩
  calc ∫ ω, f ω * f ω ∂P = ∫ y, y * y ∂(P.map f) :=
        (integral_map hf (continuous_id.mul continuous_id).aestronglyMeasurable).symm
    _ = v := by
      rw [h]
      have h4 := variance_id_gaussianReal (μ := 0) (v := v)
      rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at h4
      simpa [sq] using h4

theorem W5_LesHouchesWidth_bilin {Ω κ₁ κ₂ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (s : Finset κ₁) (t : Finset κ₂) (Y₁ : κ₁ → Ω → ℝ) (Y₂ : κ₂ → Ω → ℝ)
    (h1 : ∀ k ∈ s, MemLp (Y₁ k) 2 P) (h2 : ∀ l ∈ t, MemLp (Y₂ l) 2 P) :
    ∫ ω, (∑ k ∈ s, Y₁ k ω) * (∑ l ∈ t, Y₂ l ω) ∂P =
      ∑ k ∈ s, ∑ l ∈ t, ∫ ω, Y₁ k ω * Y₂ l ω ∂P := by
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum]
    intro l hl
    exact (h1 k hk).integrable_mul (h2 l hl)
  · intro k hk
    exact integrable_finsetSum _ fun l hl => (h1 k hk).integrable_mul (h2 l hl)

theorem W5_LesHouchesWidth_theta_map (n : ℕ → ℕ) (L : ℕ) (c : ParamIndex n L) :
    (stdGaussianParams n L).map (fun θ => θ c) = gaussianReal 0 1 := by
  unfold stdGaussianParams
  exact (measurePreserving_eval (fun _ : ParamIndex n L => gaussianReal 0 1) c).map_eq

theorem W5_LesHouchesWidth_theta_pair (n : ℕ → ℕ) (L : ℕ) (a b : ParamIndex n L) :
    ∫ θ, θ a * θ b ∂(stdGaussianParams n L) = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h
    have := (W5_LesHouchesWidth_gfacts (W5_LesHouchesWidth_theta_map n L a)).2.2.2
    simpa using this
  · have hind : iIndepFun (fun (c : ParamIndex n L) (θ : Params n L) => θ c)
        (stdGaussianParams n L) := by
      unfold stdGaussianParams
      exact iIndepFun_pi (X := fun _ y => y) (fun _ => aemeasurable_id)
    obtain ⟨ha1, -, ha3, -⟩ := W5_LesHouchesWidth_gfacts (W5_LesHouchesWidth_theta_map n L a)
    obtain ⟨hb1, -, -, -⟩ := W5_LesHouchesWidth_gfacts (W5_LesHouchesWidth_theta_map n L b)
    rw [(hind.indepFun h).integral_fun_mul_eq_mul_integral ha1.aestronglyMeasurable
      hb1.aestronglyMeasurable, ha3, zero_mul]

theorem W5_LesHouchesWidth_theta_memLp (n : ℕ → ℕ) (L : ℕ) (a : ParamIndex n L) :
    MemLp (fun θ : Params n L => θ a) 2 (stdGaussianParams n L) :=
  (W5_LesHouchesWidth_gfacts (W5_LesHouchesWidth_theta_map n L a)).2.1

theorem solution (σb σw : ℝ) (φ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (x x' : Fin (n 0) → ℝ) (i : Fin (n 1)) :
    ∫ θ, mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 i * mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 i
        ∂(stdGaussianParams n L) =
      nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x' := by
  have h0 : 0 < L + 1 := Nat.succ_pos L
  set a0 : ParamIndex n L := Sum.inl ⟨⟨0, h0⟩, i⟩ with ha0
  set aw : Fin (n 0) → ParamIndex n L := fun j => Sum.inr ⟨⟨0, h0⟩, (i, j)⟩ with haw
  have hz : ∀ (θ : Params n L) (y : Fin (n 0) → ℝ), mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 i =
      ∑ o ∈ Finset.insertNone (Finset.univ : Finset (Fin (n 0))),
        Option.elim o (Real.sqrt (σb ^ 2) * θ a0)
          (fun j => Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * y j) := by
    intro θ y
    rw [Finset.sum_insertNone]
    simp [mlpZ, mlpBias, mlpWeight, a0, aw]
  simp_rw [hz]
  have hmem : ∀ (y : Fin (n 0) → ℝ), ∀ o ∈ Finset.insertNone (Finset.univ : Finset (Fin (n 0))),
      MemLp (fun θ : Params n L => Option.elim o (Real.sqrt (σb ^ 2) * θ a0)
        (fun j => Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * y j)) 2 (stdGaussianParams n L) := by
    intro y o ho
    cases o with
    | none => exact (W5_LesHouchesWidth_theta_memLp n L a0).const_mul _
    | some j => exact ((W5_LesHouchesWidth_theta_memLp n L (aw j)).const_mul _).mul_const _
  have hB := W5_LesHouchesWidth_bilin (P := stdGaussianParams n L)
    (Finset.insertNone (Finset.univ : Finset (Fin (n 0))))
    (Finset.insertNone (Finset.univ : Finset (Fin (n 0))))
    (fun o (θ : Params n L) => Option.elim o (Real.sqrt (σb ^ 2) * θ a0)
        (fun j => Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x j))
    (fun o (θ : Params n L) => Option.elim o (Real.sqrt (σb ^ 2) * θ a0)
        (fun j => Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x' j))
    (hmem x) (hmem x')
  try simp only at hB
  rw [hB]
  simp only [Finset.sum_insertNone, Option.elim]
  have hne : ∀ j, a0 ≠ aw j := fun j => Sum.inl_ne_inr
  have hwinj : ∀ j k, aw j = aw k ↔ j = k := by
    intro j k
    constructor
    · intro h
      simp only [aw, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
      exact h
    · rintro rfl; rfl
  have hbb : ∫ θ, Real.sqrt (σb ^ 2) * θ a0 * (Real.sqrt (σb ^ 2) * θ a0) ∂(stdGaussianParams n L)
      = σb ^ 2 := by
    rw [show (fun θ : Params n L => Real.sqrt (σb ^ 2) * θ a0 * (Real.sqrt (σb ^ 2) * θ a0)) =
      fun θ => (Real.sqrt (σb ^ 2) * Real.sqrt (σb ^ 2)) * (θ a0 * θ a0) from
        funext fun θ => by ring, integral_const_mul, W5_LesHouchesWidth_theta_pair, if_pos rfl,
      mul_one, Real.mul_self_sqrt (sq_nonneg _)]
  have hbW : ∀ k, ∫ θ, Real.sqrt (σb ^ 2) * θ a0 *
      (Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw k) * x' k) ∂(stdGaussianParams n L) = 0 := by
    intro k
    rw [show (fun θ : Params n L => Real.sqrt (σb ^ 2) * θ a0 *
        (Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw k) * x' k)) =
      fun θ => (Real.sqrt (σb ^ 2) * Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * x' k) * (θ a0 * θ (aw k)) from
        funext fun θ => by ring, integral_const_mul, W5_LesHouchesWidth_theta_pair,
      if_neg (hne k), mul_zero]
  have hWb : ∀ j, ∫ θ, Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x j *
      (Real.sqrt (σb ^ 2) * θ a0) ∂(stdGaussianParams n L) = 0 := by
    intro j
    rw [show (fun θ : Params n L => Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x j *
        (Real.sqrt (σb ^ 2) * θ a0)) =
      fun θ => (Real.sqrt (σb ^ 2) * Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * x j) * (θ a0 * θ (aw j)) from
        funext fun θ => by ring, integral_const_mul, W5_LesHouchesWidth_theta_pair,
      if_neg (hne j), mul_zero]
  have hWW : ∀ j, ∑ k, ∫ θ, Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x j *
      (Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw k) * x' k) ∂(stdGaussianParams n L) =
        σw ^ 2 / (n 0 : ℝ) * (x j * x' j) := by
    intro j
    have hk : ∀ k, ∫ θ, Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x j *
        (Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw k) * x' k) ∂(stdGaussianParams n L) =
          if j = k then σw ^ 2 / (n 0 : ℝ) * (x j * x' j) else 0 := by
      intro k
      rw [show (fun θ : Params n L => Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw j) * x j *
          (Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * θ (aw k) * x' k)) =
        fun θ => (Real.sqrt (σw ^ 2 / (n 0 : ℝ)) * Real.sqrt (σw ^ 2 / (n 0 : ℝ)) *
          (x j * x' k)) * (θ (aw j) * θ (aw k)) from funext fun θ => by ring,
        integral_const_mul, W5_LesHouchesWidth_theta_pair,
        Real.mul_self_sqrt (by positivity)]
      by_cases h : j = k
      · subst h; simp
      · rw [if_neg (by rw [hwinj]; exact h), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_ite_eq]
    simp
  rw [hbb, Finset.sum_eq_zero (fun k _ => hbW k), Finset.sum_add_distrib,
    Finset.sum_eq_zero (fun j _ => hWb j), Finset.sum_congr rfl (fun j _ => hWW j)]
  simp only [nngpKernel, add_zero, zero_add]
  rw [← Finset.mul_sum]
  ring

open Matrix in
theorem W5_LesHouchesWidth_quad_aux {k d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (A : Matrix (Fin k) (Fin d) ℝ) (u v : Fin k → ℝ) :
    (A.transpose *ᵥ u) ⬝ᵥ S *ᵥ (A.transpose *ᵥ v) = u ⬝ᵥ (A * S * A.transpose) *ᵥ v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec u A]

theorem W5_LesHouchesWidth_gaussian_linear_image {k d : ℕ} (μ : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) (A : Matrix (Fin k) (Fin d) ℝ) :
    (multivariateGaussian μ S).map (Matrix.toEuclideanLin A) =
      multivariateGaussian (Matrix.toEuclideanLin A μ) (A * S * A.transpose) := by
  set Lc : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) with hLc
  have hL : (⇑(Matrix.toEuclideanLin A) : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k))
      = ⇑Lc := rfl
  have hS' : (A * S * A.transpose).PosSemidef := by
    have := hS.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hadj : ∀ u, Lc.adjoint u = Matrix.toEuclideanLin A.transpose u := by
    intro u
    have := LinearMap.adjoint_eq_toCLM_adjoint (Matrix.toEuclideanLin A)
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, this]
    rfl
  rw [hL]
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian] <;> rfl
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id Lc, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', hadj, hadj]
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    exact W5_LesHouchesWidth_quad_aux S A _ _

/-! ### Second-layer covariance -/

open Matrix in
theorem W5_LesHouchesWidth_quad_aux' {ι κ : Type*} [Fintype ι] [Fintype κ] (S : Matrix ι ι ℝ)
    (A : Matrix κ ι ℝ) (u v : κ → ℝ) :
    (A.transpose *ᵥ u) ⬝ᵥ S *ᵥ (A.transpose *ᵥ v) = u ⬝ᵥ (A * S * A.transpose) *ᵥ v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose,
    Matrix.mulVec_transpose, Matrix.dotProduct_mulVec u A]

theorem W5_LesHouchesWidth_glin {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (μ : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (A : Matrix κ ι ℝ) :
    (multivariateGaussian μ S).map (Matrix.toEuclideanLin A) =
      multivariateGaussian (Matrix.toEuclideanLin A μ) (A * S * A.transpose) := by
  set Lc : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) with hLc
  have hL : (⇑(Matrix.toEuclideanLin A) : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ)
      = ⇑Lc := rfl
  have hS' : (A * S * A.transpose).PosSemidef := by
    have := hS.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hadj : ∀ u, Lc.adjoint u = Matrix.toEuclideanLin A.transpose u := by
    intro u
    have := LinearMap.adjoint_eq_toCLM_adjoint (Matrix.toEuclideanLin A)
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, this]
    rfl
  rw [hL]
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, integral_id_multivariateGaussian] <;> rfl
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id Lc, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', hadj, hadj]
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    exact W5_LesHouchesWidth_quad_aux' S A _ _

/-- The first-layer preactivation as a linear map of the parameters. -/
noncomputable def W5_LesHouchesWidth_zl (σb σw : ℝ) (φ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (j : Fin (n 1)) (y : Fin (n 0) → ℝ) : Params n L →ₗ[ℝ] ℝ where
  toFun θ := mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 j
  map_add' θ θ' := by
    simp only [mlpZ, mlpBias, mlpWeight, Pi.add_apply]
    split_ifs
    · simp only [mul_add, add_mul, Finset.sum_add_distrib]
      ring
    · simp
  map_smul' c θ := by
    simp only [mlpZ, mlpBias, mlpWeight, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    · simp

theorem W5_LesHouchesWidth_zl_apply (σb σw : ℝ) (φ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (j : Fin (n 1)) (y : Fin (n 0) → ℝ) (θ : Params n L) :
    mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 j =
      ∑ a, θ a * W5_LesHouchesWidth_zl σb σw φ n L j y (fun b => if a = b then 1 else 0) := by
  have h := (W5_LesHouchesWidth_zl σb σw φ n L j y).pi_apply_eq_sum_univ θ
  simp only [smul_eq_mul] at h
  exact h

theorem W5_LesHouchesWidth_pairlaw (σb σw : ℝ) (φ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (j : Fin (n 1)) (y : Fin 2 → Fin (n 0) → ℝ) :
    (stdGaussianParams n L).map
        (fun θ => WithLp.toLp 2 (fun r : Fin 2 => mlpZ (σb ^ 2) (σw ^ 2) φ θ (y r) 1 j)) =
      multivariateGaussian 0 (fun r s : Fin 2 => nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (y r) (y s)) := by
  set A : Fin 2 → ParamIndex n L → ℝ := fun r a =>
    W5_LesHouchesWidth_zl σb σw φ n L j (y r) (fun b => if a = b then 1 else 0) with hA
  have hZ : (fun θ : Params n L => WithLp.toLp 2 (fun r : Fin 2 =>
      mlpZ (σb ^ 2) (σw ^ 2) φ θ (y r) 1 j)) =
      (Matrix.toEuclideanLin (Matrix.of A)) ∘ (WithLp.toLp 2) := by
    funext θ
    ext r
    simp only [Function.comp_apply, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Matrix.of_apply, W5_LesHouchesWidth_zl_apply, hA]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hstd : (stdGaussianParams n L).map (WithLp.toLp 2) =
      multivariateGaussian 0 (1 : Matrix (ParamIndex n L) (ParamIndex n L) ℝ) := by
    rw [multivariateGaussian_zero_one, stdGaussianParams]
    exact map_pi_eq_stdGaussian
  have hmom : ∀ r s : Fin 2, ∑ a, A r a * A s a =
      nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (y r) (y s) := by
    intro r s
    rw [← solution σb σw φ n L (y r) (y s) j]
    simp_rw [W5_LesHouchesWidth_zl_apply]
    have hB := W5_LesHouchesWidth_bilin (P := stdGaussianParams n L) Finset.univ Finset.univ
      (fun a (θ : Params n L) => θ a * A r a) (fun a (θ : Params n L) => θ a * A s a)
      (fun a _ => (W5_LesHouchesWidth_theta_memLp n L a).mul_const _)
      (fun a _ => (W5_LesHouchesWidth_theta_memLp n L a).mul_const _)
    try simp only at hB
    rw [hB]
    have hterm : ∀ a b, ∫ θ, θ a * A r a * (θ b * A s b) ∂(stdGaussianParams n L) =
        A r a * A s b * (if a = b then 1 else 0) := by
      intro a b
      rw [show (fun θ : Params n L => θ a * A r a * (θ b * A s b)) =
        fun θ => (A r a * A s b) * (θ a * θ b) from funext fun θ => by ring,
        integral_const_mul, W5_LesHouchesWidth_theta_pair]
    simp only [hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hZ, ← Measure.map_map (by fun_prop) (by fun_prop), hstd,
    W5_LesHouchesWidth_glin _ _ Matrix.PosSemidef.one]
  simp only [map_zero, Matrix.mul_one]
  congr 1
  funext r s
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  exact hmom r s

theorem W5_LesHouchesWidth_kern_symm (σb σw : ℝ) (φ : ℝ → ℝ) {n0 : ℕ} (x x' : Fin n0 → ℝ) :
    nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x' x = nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x' := by
  simp only [nngpKernel]
  congr 3
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem W5_LesHouchesWidth_pairavg (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ) (n : ℕ → ℕ)
    (L : ℕ) (j : Fin (n 1)) (x x' : Fin (n 0) → ℝ) :
    ∫ θ, φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 j) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 j)
        ∂(stdGaussianParams n L) =
      gaussPairAvg φ (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x) (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x')
        (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x' x') := by
  have hlaw := W5_LesHouchesWidth_pairlaw σb σw φ n L j ![x, x']
  have hmeasZ : Measurable (fun θ : Params n L => WithLp.toLp 2 (fun r : Fin 2 =>
      mlpZ (σb ^ 2) (σw ^ 2) φ θ (![x, x'] r) 1 j)) := by
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun r => ?_)
    exact (W5_LesHouchesWidth_zl σb σw φ n L j (![x, x'] r)).continuous_of_finiteDimensional.measurable
  have hF : Measurable (fun u : EuclideanSpace ℝ (Fin 2) => φ (u 0) * φ (u 1)) := by fun_prop
  have e : (fun r s : Fin 2 => nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (![x, x'] r) (![x, x'] s)) =
      !![nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x, nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x';
        nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x', nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x' x'] := by
    funext r s
    fin_cases r <;> fin_cases s <;> simp [W5_LesHouchesWidth_kern_symm]
  rw [e] at hlaw
  unfold gaussPairAvg
  rw [← hlaw, integral_map hmeasZ.aemeasurable hF.aestronglyMeasurable]
  rfl

theorem W5_LesHouchesWidth_marg1 (σb σw : ℝ) (φ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (j : Fin (n 1)) (x : Fin (n 0) → ℝ) :
    (stdGaussianParams n L).map (fun θ => mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 j) =
      gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x).toNNReal := by
  have hlaw := W5_LesHouchesWidth_pairlaw σb σw φ n L j ![x, x]
  have hmeasZ : Measurable (fun θ : Params n L => WithLp.toLp 2 (fun r : Fin 2 =>
      mlpZ (σb ^ 2) (σw ^ 2) φ θ (![x, x] r) 1 j)) := by
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ fun r => ?_)
    exact (W5_LesHouchesWidth_zl σb σw φ n L j (![x, x] r)).continuous_of_finiteDimensional.measurable
  have hS : Matrix.PosSemidef (fun r s : Fin 2 =>
      nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (![x, x] r) (![x, x] s)) := by
    have hk : (fun r s : Fin 2 => nngpKernel (σb ^ 2) (σw ^ 2) φ 1 (![x, x] r) (![x, x] s)) =
        fun _ _ => nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x := by
      funext r s
      fin_cases r <;> fin_cases s <;> rfl
    have hnn : 0 ≤ nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x := by
      rw [← solution σb σw φ n L x x j]
      exact integral_nonneg fun θ => mul_self_nonneg _
    rw [hk]
    generalize nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x = κ at hnn ⊢
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · exact Matrix.IsHermitian.ext fun _ _ => by simp
    · simp only [star_trivial, dotProduct, Matrix.mulVec]
      have : ∑ i, v i * ∑ k, κ * v k = κ * (∑ i, v i) ^ 2 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
      rw [this]
      positivity
  have h0 := (measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := (0 : Fin 2))).map_eq
  rw [← hlaw, Measure.map_map (by fun_prop) hmeasZ] at h0
  simp only [PiLp.zero_apply] at h0
  exact h0

theorem W5_LesHouchesWidth_indepmul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : MemLp X 2 P)
    (hY : MemLp Y 2 P) : MemLp (fun ω => X ω * Y ω) 2 P := by
  have hXs : Integrable (fun ω => X ω ^ 2) P := (memLp_two_iff_integrable_sq hX.1).1 hX
  have hYs : Integrable (fun ω => Y ω ^ 2) P := (memLp_two_iff_integrable_sq hY.1).1 hY
  have hind := hXY.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hprod := hind.integrable_mul hXs hYs
  refine (memLp_two_iff_integrable_sq (hX.1.mul hY.1)).2 ?_
  refine hprod.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Function.comp_apply, id, Pi.mul_apply]
  ring

theorem W5_LesHouchesWidth_covariance_second_layer (σb σw : ℝ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (n : ℕ → ℕ) (L : ℕ) (hL : 1 ≤ L) (hn : 1 ≤ n 1)
    (x x' : Fin (n 0) → ℝ)
    (hφx : Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x).toNNReal))
    (hφx' : Integrable (fun u => φ u ^ 2)
      (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x' x').toNNReal))
    (i : Fin (n 2)) :
    ∫ θ, mlpZ (σb ^ 2) (σw ^ 2) φ θ x 2 i * mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 2 i
        ∂(stdGaussianParams n L) =
      nngpKernel (σb ^ 2) (σw ^ 2) φ 2 x x' := by
  set μ := stdGaussianParams n L with hμ
  have h1 : 1 < L + 1 := by omega
  set lay : ParamIndex n L → ℕ := fun a => Sum.elim (fun p => p.1.val) (fun p => p.1.val) a
    with hlay
  set S0 : Finset (ParamIndex n L) := Finset.univ.filter (fun a => lay a = 0) with hS0
  set S1 : Finset (ParamIndex n L) := Finset.univ.filter (fun a => lay a = 1) with hS1
  have hdisj : Disjoint S0 S1 := by
    rw [hS0, hS1, Finset.disjoint_filter]
    intro a _ h0 h1'
    omega
  have hC : iIndepFun (fun (c : ParamIndex n L) (θ : Params n L) => θ c) μ := by
    rw [hμ]
    unfold stdGaussianParams
    exact iIndepFun_pi (X := fun _ y => y) (fun _ => aemeasurable_id)
  have hind := hC.indepFun_finset S1 S0 hdisj.symm
    (fun c => measurable_pi_apply c)
  -- extension of a layer-0 tuple
  let ext0 : (S0 → ℝ) → Params n L := fun v a => if h : a ∈ S0 then v ⟨a, h⟩ else 0
  have hext0 : Measurable ext0 := by
    refine measurable_pi_lambda _ fun a => ?_
    by_cases h : a ∈ S0
    · simp only [ext0, dif_pos h]; exact measurable_pi_apply _
    · simp only [ext0, dif_neg h]; exact measurable_const
  have hz1 : ∀ (y : Fin (n 0) → ℝ) (jj : Fin (n 1)) (θ : Params n L),
      mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj =
        mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 (fun q => θ q.1)) y 1 jj := by
    intro y jj θ
    simp [mlpZ, mlpBias, mlpWeight, ext0, hS0, hlay]
  have hΨ : ∀ (y : Fin (n 0) → ℝ) (jj : Fin (n 1)),
      Measurable (fun v : S0 → ℝ => mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) y 1 jj) :=
    fun y jj => (W5_LesHouchesWidth_zl σb σw φ n L jj y).continuous_of_finiteDimensional.measurable.comp hext0
  have hfac : ∀ (Φ : (S1 → ℝ) → ℝ) (Ψ : (S0 → ℝ) → ℝ), Measurable Φ → Measurable Ψ →
      ∫ θ, Φ (fun q => θ q.1) * Ψ (fun q => θ q.1) ∂μ =
        (∫ θ, Φ (fun q => θ q.1) ∂μ) * ∫ θ, Ψ (fun q => θ q.1) ∂μ := by
    intro Φ Ψ hΦ hΨm
    have key := (hind.comp hΦ hΨm).integral_fun_mul_eq_mul_integral
      (hΦ.comp (measurable_pi_lambda _ fun q => measurable_pi_apply _)).aestronglyMeasurable
      (hΨm.comp (measurable_pi_lambda _ fun q => measurable_pi_apply _)).aestronglyMeasurable
    simp only [Function.comp_apply] at key
    exact key
  -- layer-1 coordinates
  have memb : ∀ ii : Fin (n 2), (Sum.inl ⟨⟨1, h1⟩, ii⟩ : ParamIndex n L) ∈ S1 := by
    intro ii; simp [hS1, hlay]
  have memw : ∀ (ii : Fin (n 2)) (jj : Fin (n 1)),
      (Sum.inr ⟨⟨1, h1⟩, (ii, jj)⟩ : ParamIndex n L) ∈ S1 := by
    intro ii jj; simp [hS1, hlay]
  -- integrability of the activations
  have hφL2 : ∀ (y : Fin (n 0) → ℝ) (jj : Fin (n 1)),
      Integrable (fun u => φ u ^ 2)
        (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 y y).toNNReal) →
      MemLp (fun θ => φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj)) 2 μ := by
    intro y jj hint
    have hmz : Measurable (fun θ : Params n L => mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj) :=
      (W5_LesHouchesWidth_zl σb σw φ n L jj y).continuous_of_finiteDimensional.measurable
    rw [← W5_LesHouchesWidth_marg1 σb σw φ n L jj y] at hint
    have h2 := (integrable_map_measure (hφ.pow_const 2).aestronglyMeasurable
      hmz.aemeasurable).1 hint
    exact (memLp_two_iff_integrable_sq (hφ.comp hmz).aestronglyMeasurable).2 h2
  have hAx := hφL2 x
  have hAx' := hφL2 x'
  -- the second-layer preactivation as a finite sum
  have hz2 : ∀ (θ : Params n L) (y : Fin (n 0) → ℝ),
      mlpZ (σb ^ 2) (σw ^ 2) φ θ y 2 i =
        ∑ o ∈ Finset.insertNone (Finset.univ : Finset (Fin (n 1))),
          Option.elim o (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩))
            (fun jj => Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
              φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj)) := by
    intro θ y
    rw [Finset.sum_insertNone]
    simp only [Option.elim]
    conv_lhs => rw [mlpZ]
    simp [mlpBias, mlpWeight, h1]
  simp_rw [hz2]
  have hmemT : ∀ (y : Fin (n 0) → ℝ),
      Integrable (fun u => φ u ^ 2)
        (gaussianReal 0 (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 y y).toNNReal) →
      ∀ o ∈ Finset.insertNone (Finset.univ : Finset (Fin (n 1))),
      MemLp (fun θ : Params n L => Option.elim o (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩))
            (fun jj => Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
              φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj))) 2 μ := by
    intro y hint o _
    cases o with
    | none => exact (W5_LesHouchesWidth_theta_memLp n L _).const_mul _
    | some jj =>
      have hind' : IndepFun (fun θ : Params n L => θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩))
          (fun θ => φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj)) μ := by
        have hm1 : Measurable (fun v : S1 → ℝ => v ⟨Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩, memw i jj⟩) :=
          measurable_pi_apply _
        have hm2 : Measurable (fun v : S0 → ℝ => φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) y 1 jj)) :=
          hφ.comp (hΨ y jj)
        have := hind.comp hm1 hm2
        refine this.congr (Filter.Eventually.of_forall fun θ => rfl)
          (Filter.Eventually.of_forall fun θ => ?_)
        simp only [Function.comp_apply]
        rw [← hz1 y jj θ]
      have := W5_LesHouchesWidth_indepmul hind' (W5_LesHouchesWidth_theta_memLp n L _)
        (hφL2 y jj hint)
      refine MemLp.ae_eq (Filter.Eventually.of_forall fun θ => ?_)
        (this.const_mul (Real.sqrt (σw ^ 2 / (n 1 : ℝ))))
      simp only [Option.elim]
      ring
  have hB := W5_LesHouchesWidth_bilin (P := μ)
    (Finset.insertNone (Finset.univ : Finset (Fin (n 1))))
    (Finset.insertNone (Finset.univ : Finset (Fin (n 1))))
    (fun o (θ : Params n L) => Option.elim o (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩))
            (fun jj => Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
              φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj)))
    (fun o (θ : Params n L) => Option.elim o (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩))
            (fun jj => Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
              φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 jj)))
    (hmemT x hφx) (hmemT x' hφx')
  try simp only at hB
  rw [hB]
  simp only [Finset.sum_insertNone, Option.elim]
  -- evaluate the terms
  have hbb : ∫ θ, Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩) *
      (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩)) ∂μ = σb ^ 2 := by
    rw [show (fun θ : Params n L => Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩) *
      (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩))) =
      fun θ => (Real.sqrt (σb ^ 2) * Real.sqrt (σb ^ 2)) *
        (θ (Sum.inl ⟨⟨1, h1⟩, i⟩) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩)) from funext fun θ => by ring,
      integral_const_mul, W5_LesHouchesWidth_theta_pair, if_pos rfl, mul_one,
      Real.mul_self_sqrt (sq_nonneg _)]
  have hcross : ∀ (y : Fin (n 0) → ℝ) (jj : Fin (n 1)),
      ∫ θ, θ (Sum.inl ⟨⟨1, h1⟩, i⟩) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj) ∂μ = 0 := by
    intro y jj
    have key := hfac (fun v => v ⟨_, memb i⟩ * v ⟨_, memw i jj⟩)
      (fun v => φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) y 1 jj)) (by fun_prop) (hφ.comp (hΨ y jj))
    have e : ∀ θ : Params n L, θ (Sum.inl ⟨⟨1, h1⟩, i⟩) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ y 1 jj) =
        (fun v : S1 → ℝ => v ⟨_, memb i⟩ * v ⟨_, memw i jj⟩) (fun q => θ q.1) *
        (fun v : S0 → ℝ => φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) y 1 jj)) (fun q => θ q.1) := by
      intro θ
      simp only
      rw [hz1 y jj θ]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), key]
    simp only
    rw [W5_LesHouchesWidth_theta_pair, if_neg Sum.inl_ne_inr, zero_mul]
  have hbW : ∀ jj : Fin (n 1), ∫ θ, Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩) *
      (Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 jj)) ∂μ = 0 := by
    intro jj
    rw [show (fun θ : Params n L => Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩) *
      (Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 jj))) =
      fun θ => (Real.sqrt (σb ^ 2) * Real.sqrt (σw ^ 2 / (n 1 : ℝ))) *
        (θ (Sum.inl ⟨⟨1, h1⟩, i⟩) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
          φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 jj)) from funext fun θ => by ring,
      integral_const_mul, hcross, mul_zero]
  have hWb : ∀ jj : Fin (n 1), ∫ θ, Real.sqrt (σw ^ 2 / (n 1 : ℝ)) *
      θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) *
      (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩)) ∂μ = 0 := by
    intro jj
    rw [show (fun θ : Params n L => Real.sqrt (σw ^ 2 / (n 1 : ℝ)) *
      θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) *
      (Real.sqrt (σb ^ 2) * θ (Sum.inl ⟨⟨1, h1⟩, i⟩))) =
      fun θ => (Real.sqrt (σb ^ 2) * Real.sqrt (σw ^ 2 / (n 1 : ℝ))) *
        (θ (Sum.inl ⟨⟨1, h1⟩, i⟩) * θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) *
          φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj)) from funext fun θ => by ring,
      integral_const_mul, hcross, mul_zero]
  have hWW : ∀ jj kk : Fin (n 1), ∫ θ, Real.sqrt (σw ^ 2 / (n 1 : ℝ)) *
      θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) *
      (Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, kk)⟩) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 kk)) ∂μ =
      if jj = kk then σw ^ 2 / (n 1 : ℝ) * ∫ θ, φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 jj) ∂μ else 0 := by
    intro jj kk
    have key := hfac (fun v => v ⟨_, memw i jj⟩ * v ⟨_, memw i kk⟩)
      (fun v => φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) x 1 jj) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) x' 1 kk)) (by fun_prop)
      ((hφ.comp (hΨ x jj)).mul (hφ.comp (hΨ x' kk)))
    rw [show (fun θ : Params n L => Real.sqrt (σw ^ 2 / (n 1 : ℝ)) *
      θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) *
      (Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * θ (Sum.inr ⟨⟨1, h1⟩, (i, kk)⟩) *
        φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 kk))) =
      fun θ => (Real.sqrt (σw ^ 2 / (n 1 : ℝ)) * Real.sqrt (σw ^ 2 / (n 1 : ℝ))) *
        (θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) * θ (Sum.inr ⟨⟨1, h1⟩, (i, kk)⟩) *
          (φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 kk)))
        from funext fun θ => by ring, integral_const_mul]
    have e : ∀ θ : Params n L, θ (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩) * θ (Sum.inr ⟨⟨1, h1⟩, (i, kk)⟩) *
        (φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) * φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 kk)) =
        (fun v : S1 → ℝ => v ⟨_, memw i jj⟩ * v ⟨_, memw i kk⟩) (fun q => θ q.1) *
        (fun v : S0 → ℝ => φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) x 1 jj) *
          φ (mlpZ (σb ^ 2) (σw ^ 2) φ (ext0 v) x' 1 kk)) (fun q => θ q.1) := by
      intro θ
      simp only
      rw [hz1 x jj θ, hz1 x' kk θ]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), key]
    simp only
    rw [W5_LesHouchesWidth_theta_pair, Real.mul_self_sqrt (by positivity)]
    by_cases h : jj = kk
    · subst h
      simp only [if_true, one_mul]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only
      rw [← hz1 x jj θ, ← hz1 x' jj θ]
    · have hne : (Sum.inr ⟨⟨1, h1⟩, (i, jj)⟩ : ParamIndex n L) ≠
          Sum.inr ⟨⟨1, h1⟩, (i, kk)⟩ := by
        intro heq
        apply h
        simpa using heq
      simp only [if_neg hne, if_neg h, zero_mul, mul_zero]
  rw [hbb, Finset.sum_eq_zero (fun jj _ => hbW jj), Finset.sum_add_distrib,
    Finset.sum_eq_zero (fun jj _ => hWb jj)]
  simp only [hWW, Finset.sum_ite_eq, Finset.mem_univ, if_true, add_zero, zero_add]
  have hpa : ∀ jj : Fin (n 1), ∫ θ, φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x 1 jj) *
      φ (mlpZ (σb ^ 2) (σw ^ 2) φ θ x' 1 jj) ∂μ =
      gaussPairAvg φ (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x) (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x x')
        (nngpKernel (σb ^ 2) (σw ^ 2) φ 1 x' x') :=
    fun jj => W5_LesHouchesWidth_pairavg σb σw φ hφ n L jj x x'
  simp only [hpa, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [nngpKernel]
  have hn1 : (n 1 : ℝ) ≠ 0 := by exact_mod_cast (show n 1 ≠ 0 by omega)
  field_simp
