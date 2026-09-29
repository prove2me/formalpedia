-- Prove2me | solution 1 for HighDimProb.Isoperimetry.random_projection_concentration
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T06:03:59.457987+00:00
-- url     : https://prove2.me/submissions/46345aef-75cc-4608-a4ca-5c2f2bbba0fa

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

theorem rpc0b_sq_norm_eq_inner {n : ℕ} (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p) (z : EuclideanSpace ℝ (Fin n)) :
    ‖p z‖ ^ 2 = inner ℝ z (p z) := by
  have hsym := hs.isSymmetric
  have hpp : p (p z) = p z := by
    have := congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => q z) hi
    simpa using this
  rw [← real_inner_self_eq_norm_sq]
  have := hsym z (p z)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this, hpp]

theorem rpc0b_norm_le {n : ℕ} (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p) (z : EuclideanSpace ℝ (Fin n)) :
    ‖p z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have h1 := rpc0b_sq_norm_eq_inner p hi hs z
  have h2 : inner ℝ z (p z) ≤ ‖z‖ * ‖p z‖ := real_inner_le_norm _ _
  have h3 : ‖p z‖ ≤ ‖z‖ := by
    rcases (norm_nonneg (p z)).eq_or_lt with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem rpc0b_gauss_sq_int (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, mul_assoc, ← Real.exp_add]
    congr 2
    · simp
    · push_cast; ring
  constructor
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
    have : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • Real.exp (t * x ^ 2))
        = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
      funext x
      rw [toReal_gaussianPDF, smul_eq_mul, hpt]
    rw [this]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, hpt]
    rw [integral_const_mul, integral_gaussian]
    have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
    have h3 : (0 : ℝ) < 1 - 2 * t := by linarith
    rw [show Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) by field_simp]
    rw [Real.sqrt_div h2.le, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 h2).ne', one_mul]

theorem rpc0b_exp_bound (t : ℝ) (ht : |t| ≤ 1 / 4) :
    (Real.sqrt (1 - 2 * t))⁻¹ ≤ Real.exp (t + 2 * t ^ 2) := by
  have h1 : 0 < 1 - 2 * t := by
    have := (abs_le.1 ht).2; linarith
  have key : 1 ≤ (1 - 2 * t) * Real.exp (2 * t + 4 * t ^ 2) := by
    rcases le_or_gt t 0 with h0 | h0
    · have := Real.add_one_le_exp (2 * t + 4 * t ^ 2)
      nlinarith [sq_nonneg t, mul_nonneg (neg_nonneg.2 h0) (sq_nonneg t)]
    · have hs : 0 ≤ 2 * t + 4 * t ^ 2 := by positivity
      have := Real.quadratic_le_exp_of_nonneg hs
      have ht4 : t ≤ 1 / 4 := (abs_le.1 ht).2
      nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0, mul_pos (mul_pos (mul_pos h0 h0) h0) h0,
        mul_nonneg (sub_nonneg.2 ht4) (mul_pos (mul_pos h0 h0) h0).le,
        mul_nonneg (sub_nonneg.2 ht4) (mul_pos (mul_pos (mul_pos h0 h0) h0) h0).le,
        mul_nonneg (sub_nonneg.2 ht4) (mul_pos h0 h0).le]
  have hs : 0 < Real.sqrt (1 - 2 * t) := Real.sqrt_pos.2 h1
  have he : Real.exp (2 * t + 4 * t ^ 2) = Real.exp (t + 2 * t ^ 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [inv_le_iff_one_le_mul₀ hs]
  have hsq : Real.sqrt (1 - 2 * t) ^ 2 = 1 - 2 * t := Real.sq_sqrt h1.le
  rw [he] at key
  have hpos : 0 ≤ Real.sqrt (1 - 2 * t) * Real.exp (t + 2 * t ^ 2) := by positivity
  nlinarith [sq_nonneg (Real.sqrt (1 - 2 * t) * Real.exp (t + 2 * t ^ 2) - 1)]

theorem rpc0b_eigen {n : ℕ} (m : ℕ) (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p)
    (hr : Module.finrank ℝ (LinearMap.range (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (l : Fin n → ℝ),
      (∀ i, l i = 0 ∨ l i = 1) ∧ ∑ i, l i = (m : ℝ) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖p v‖ ^ 2 = ∑ i, l i * (b.repr v i) ^ 2 ∧
        ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) with hTdef
  have hT : T.IsSymmetric := hs.isSymmetric
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set b := hT.eigenvectorBasis hn with hb
  set l := hT.eigenvalues hn with hl
  have hTT : ∀ x, T (T x) = T x := by
    intro x
    have := congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => q x) hi
    simpa [hTdef] using this
  have hl01 : ∀ i, l i = 0 ∨ l i = 1 := by
    intro i
    have h1 : T (b i) = (l i : ℝ) • b i := hT.apply_eigenvectorBasis hn i
    have h2 := hTT (b i)
    rw [h1, map_smul, h1, smul_smul] at h2
    have hne : b i ≠ 0 := by
      intro h0
      have := b.orthonormal.1 i
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have h3 : l i * l i = l i := by
      by_contra hc
      apply hne
      have h4 : (l i * l i - l i) • b i = 0 := by rw [sub_smul, h2, sub_self]
      exact (smul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hc)
    rcases mul_eq_zero.1 (show l i * (l i - 1) = 0 by linarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  refine ⟨b, l, hl01, ?_, ?_⟩
  · have hil : IsIdempotentElem T := by
      show _ * _ = _
      exact LinearMap.ext (fun x => hTT x)
    have htr := (LinearMap.IsIdempotentElem.isProj_range _ hil).trace
    rw [LinearMap.trace_eq_sum_inner _ b, hr] at htr
    rw [← htr]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hT.apply_eigenvectorBasis hn i, inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i]
    simp [hl]
  · intro v
    have hnv : ‖v‖ ^ 2 = ∑ i, (b.repr v i) ^ 2 := by
      rw [← b.repr.norm_map v, EuclideanSpace.real_norm_sq_eq]
    refine ⟨?_, hnv⟩
    have : ‖p v‖ ^ 2 = ∑ i, (b.repr (T v) i) ^ 2 := by
      rw [← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hT.eigenvectorBasis_apply_self_apply hn v i, ← hl, ← hb]
    rcases hl01 i with h | h <;> simp [h]

theorem rpc0b_gauss_quad {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (c : Fin n → ℝ) (hc : ∀ i, |c i| ≤ 1 / 4) :
    Integrable (fun v : EuclideanSpace ℝ (Fin n) => Real.exp (∑ i, c i * (b.repr v i) ^ 2))
        (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      ∫ v, Real.exp (∑ i, c i * (b.repr v i) ^ 2) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))
        ≤ Real.exp (∑ i, (c i + 2 * c i ^ 2)) := by
  set φ : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := fun x => ∑ i, x i • b i with hφ
  have hφm : Measurable φ := by fun_prop
  have hrep : ∀ x : Fin n → ℝ, ∀ i, b.repr (φ x) i = x i := by
    intro x i
    have : φ x = b.repr.symm (WithLp.toLp 2 x) := by
      rw [hφ, ← b.sum_repr_symm]
    rw [this, LinearIsometryEquiv.apply_symm_apply]
  have hc2 : ∀ i, c i < 1 / 2 := fun i => by linarith [(abs_le.1 (hc i)).2]
  have hG := stdGaussian_eq_map_pi_orthonormalBasis b
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun v => Real.exp (∑ i, c i * (b.repr v i) ^ 2) with hF
  have hFc : Continuous F := by
    simp only [hF]
    fun_prop
  have hFφ : ∀ x, F (φ x) = ∏ i, Real.exp (c i * (x i) ^ 2) := by
    intro x
    simp only [hF, hrep, Real.exp_sum]
  have hint1 : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (c i * (x i) ^ 2))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    Integrable.fintype_prod (f := fun i (y : ℝ) => Real.exp (c i * y ^ 2))
      (fun i => (rpc0b_gauss_sq_int (c i) (hc2 i)).1)
  constructor
  · rw [hG, integrable_map_measure hFc.aestronglyMeasurable hφm.aemeasurable]
    have : F ∘ φ = fun x => ∏ i, Real.exp (c i * (x i) ^ 2) := funext hFφ
    rw [this]
    exact hint1
  · rw [hG, integral_map hφm.aemeasurable hFc.aestronglyMeasurable]
    simp_rw [hFφ]
    rw [integral_fintype_prod_eq_prod (f := fun i (y : ℝ) => Real.exp (c i * y ^ 2))]
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le)) (fun i _ => ?_)
    rw [(rpc0b_gauss_sq_int (c i) (hc2 i)).2]
    exact rpc0b_exp_bound (c i) (hc i)

theorem rpc0b_norm_le' {n : ℕ} (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p) (z : EuclideanSpace ℝ (Fin n)) :
    ‖p z‖ ≤ ‖z‖ :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (rpc0b_norm_le p hi hs z)

theorem rpc0b_inv_set {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω)
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : HighDimProb.Isoperimetry.IsUniformProjection Prob m P)
    (S : Set ℝ) (hS : MeasurableSet S) (z w : EuclideanSpace ℝ (Fin n)) (hwz : ‖w‖ = ‖z‖) :
    Prob {ω | ‖P ω z‖ ∈ S} = Prob {ω | ‖P ω w‖ ∈ S} := by
  set U := Submodule.reflection (ℝ ∙ (w - z))ᗮ with hU
  have hUw : U w = z := Submodule.reflection_sub hwz
  have hUz : U.symm z = w := by rw [← hUw, LinearIsometryEquiv.symm_apply_apply]
  have hmap := hP.2.2.2.2 U
  set G : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := {q | ‖q z‖ ∈ S} with hG
  have hGm : MeasurableSet G := by
    have hc : Continuous (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => ‖q z‖) := by
      fun_prop
    exact hc.measurable hS
  have hQ : Measurable (fun ω => (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        ((P ω).comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) := by
    have hc : Continuous (fun p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        (p.comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :=
      continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
    exact hc.measurable.comp hP.1
  have e1 := Measure.map_apply hQ hGm (μ := Prob)
  have e2 := Measure.map_apply hP.1 hGm (μ := Prob)
  rw [hmap, e2] at e1
  rw [show {ω | ‖P ω z‖ ∈ S} = P ⁻¹' G from rfl, e1]
  congr 1
  ext ω
  simp [hG, hUz]

theorem rpc0b_fubini {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : HighDimProb.Isoperimetry.IsUniformProjection Prob m P)
    (S : Set ℝ) (hS : MeasurableSet S) (z : EuclideanSpace ℝ (Fin n)) (M : ENNReal)
    (hM : ∀ p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), IsIdempotentElem p → IsSelfAdjoint p →
      Module.finrank ℝ (LinearMap.range (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m →
      stdGaussian (EuclideanSpace ℝ (Fin n))
        {x | ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ S} ≤ M) :
    Prob {ω | ‖P ω z‖ ∈ S} ≤ M := by
  set w : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => if x = 0 then z else (‖z‖ / ‖x‖) • x with hw
  have hwn : ∀ x, ‖w x‖ = ‖z‖ := by
    intro x
    by_cases hx : x = 0
    · simp [hw, hx]
    · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp only [hw, hx, if_false, norm_smul, norm_div, norm_norm]
      field_simp
  have hwm : Measurable w := by
    refine Measurable.ite (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin n))) measurable_const ?_
    exact (measurable_const.div measurable_norm).smul measurable_id
  set γ := stdGaussian (EuclideanSpace ℝ (Fin n)) with hγ
  set T : Set (Ω × EuclideanSpace ℝ (Fin n)) := {q | ‖P q.1 (w q.2)‖ ∈ S} with hT
  have hTm : MeasurableSet T := by
    have h1 : Measurable (fun q : Ω × EuclideanSpace ℝ (Fin n) => P q.1 (w q.2)) :=
      ContinuousLinearMap.measurable_apply₂.comp ((hP.1.comp measurable_fst).prodMk (hwm.comp measurable_snd))
    exact (measurable_norm.comp h1) hS
  have hconst : ∀ x, Prob {ω | ‖P ω (w x)‖ ∈ S} = Prob {ω | ‖P ω z‖ ∈ S} :=
    fun x => (rpc0b_inv_set Prob m P hP S hS z (w x) (hwn x)).symm
  calc Prob {ω | ‖P ω z‖ ∈ S} = ∫⁻ x, Prob {ω | ‖P ω (w x)‖ ∈ S} ∂γ := by
        simp only [hconst, lintegral_const, measure_univ, mul_one]
    _ = (Prob.prod γ) T := by
        rw [Measure.prod_apply_symm hTm]
        rfl
    _ = ∫⁻ ω, γ (Prod.mk ω ⁻¹' T) ∂Prob := Measure.prod_apply hTm
    _ ≤ ∫⁻ _ω, M ∂Prob := by
        refine lintegral_mono_ae ?_
        filter_upwards [hP.2.1, hP.2.2.1, hP.2.2.2.1] with ω h1 h2 h3
        exact hM (P ω) h1 h2 h3
    _ = M := by simp

theorem rpc0b_arith_up (m n ε A θ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hA0 : 0 ≤ A)
    (hA1 : A ≤ 1) (hnA : n * A = (1 + ε) ^ 2 * m) (hθ : θ = ε / (8 * (1 + ε))) :
    (θ * (1 - A) + 2 * θ ^ 2 * (1 - A) ^ 2) * m + (-θ * A + 2 * θ ^ 2 * A ^ 2) * (n - m)
      ≤ -(ε ^ 2 * m / 16) := by
  have hθs : θ * (1 + ε) = ε / 8 := by rw [hθ]; field_simp
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hre : (θ * (1 - A) + 2 * θ ^ 2 * (1 - A) ^ 2) * m + (-θ * A + 2 * θ ^ 2 * A ^ 2) * (n - m)
      = θ * (m - n * A) + 2 * θ ^ 2 * (m - 2 * m * A + A * (n * A)) := by ring
  rw [hre, hnA]
  have h1 : m - 2 * m * A + A * ((1 + ε) ^ 2 * m) ≤ (1 + (1 + ε) ^ 2) * m := by
    nlinarith [mul_nonneg hm hA0, mul_nonneg (sub_nonneg.2 hA1) (mul_nonneg (sq_nonneg (1 + ε)) hm)]
  have h2 : θ * (m - (1 + ε) ^ 2 * m) = -(ε ^ 2 * m / 8) - ε * θ * m := by
    linear_combination (-ε * m) * hθs
  have h3 : θ ^ 2 * (1 + ε) ^ 2 = ε ^ 2 / 64 := by
    linear_combination (θ * (1 + ε) + ε / 8) * hθs
  have h4 : θ ^ 2 ≤ θ ^ 2 * (1 + ε) ^ 2 := by
    have : 1 ≤ (1 + ε) ^ 2 := by nlinarith
    nlinarith [sq_nonneg θ]
  have h5 : 0 ≤ ε * θ * m := by positivity
  have h6 : 2 * θ ^ 2 * (m - 2 * m * A + A * ((1 + ε) ^ 2 * m)) ≤ 2 * θ ^ 2 * ((1 + (1 + ε) ^ 2) * m) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right h4 hm]

theorem rpc0b_arith_low (m n ε B θ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hm : 0 ≤ m) (hmn : m ≤ n)
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hnB : n * B = (1 - ε) ^ 2 * m) (hθ : θ = ε / 8) :
    (θ * (B - 1) + 2 * θ ^ 2 * (B - 1) ^ 2) * m + (θ * B + 2 * θ ^ 2 * B ^ 2) * (n - m)
      ≤ -(ε ^ 2 * m / 16) := by
  have hre : (θ * (B - 1) + 2 * θ ^ 2 * (B - 1) ^ 2) * m + (θ * B + 2 * θ ^ 2 * B ^ 2) * (n - m)
      = θ * (n * B - m) + 2 * θ ^ 2 * (m * (1 - B) ^ 2 + (n - m) * B ^ 2) := by ring
  rw [hre, hnB, hθ]
  have hn0 : 0 ≤ n := le_trans hm hmn
  have h1 : m * (1 - B) ^ 2 ≤ m := by
    have : (1 - B) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h2 : (n - m) * B ^ 2 ≤ m := by
    have e1 : (n - m) * B ^ 2 ≤ n * B := by
      nlinarith [mul_nonneg (sub_nonneg.2 hmn) (sq_nonneg B), mul_nonneg hm (sq_nonneg B),
        mul_nonneg hn0 (mul_nonneg hB0 (sub_nonneg.2 hB1))]
    have e2 : (1 - ε) ^ 2 * m ≤ m := by
      have : (1 - ε) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith
  have h3 : 2 * (ε / 8) ^ 2 * (m * (1 - B) ^ 2 + (n - m) * B ^ 2) ≤ 2 * (ε / 8) ^ 2 * (2 * m) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : ε ^ 3 * m ≤ ε ^ 2 * m := by
    have : ε ^ 3 ≤ ε ^ 2 := by nlinarith [sq_nonneg ε]
    exact mul_le_mul_of_nonneg_right this hm
  nlinarith

theorem rpc0b_sum_split {n : ℕ} (l : Fin n → ℝ) (hl01 : ∀ i, l i = 0 ∨ l i = 1) (m : ℕ)
    (hsum : ∑ i, l i = (m : ℝ)) (cc : Fin n → ℝ) (α β : ℝ)
    (hcc : ∀ i, cc i + 2 * cc i ^ 2 = α * l i + β * (1 - l i)) :
    ∑ i, (cc i + 2 * cc i ^ 2) = α * m + β * ((n : ℝ) - m) := by
  simp_rw [hcc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
  simp

theorem rpc0b_m_le_n {n : ℕ} (l : Fin n → ℝ) (hl01 : ∀ i, l i = 0 ∨ l i = 1) (m : ℕ)
    (hsum : ∑ i, l i = (m : ℝ)) : (m : ℝ) ≤ n := by
  rw [← hsum]
  calc ∑ i, l i ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by rcases hl01 i with h | h <;> rw [h] <;> norm_num)
    _ = n := by simp

theorem rpc0b_up_gauss {n : ℕ} (m : ℕ) (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p)
    (hr : Module.finrank ℝ (LinearMap.range (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    stdGaussian (EuclideanSpace ℝ (Fin n))
        {x | ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Ioi ((1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)}
      ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * m / 16))) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim z 0) hz
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨b, l, hl01, hsum, hrep⟩ := rpc0b_eigen m p hi hs hr
  set c := (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) with hcdef
  have hc0 : 0 ≤ c := by positivity
  by_cases hc1 : 1 ≤ c
  · have hempty : {x : EuclideanSpace ℝ (Fin n) |
        ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Ioi (c * ‖z‖)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
      have hw : ‖(if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ = ‖z‖ := by
        by_cases hx : x = 0
        · simp [hx]
        · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
          simp only [hx, if_false, norm_smul, norm_div, norm_norm]
          field_simp
      calc ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ≤ ‖(if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ :=
            rpc0b_norm_le' p hi hs _
        _ = ‖z‖ := hw
        _ ≤ c * ‖z‖ := le_mul_of_one_le_left (norm_nonneg _) hc1
    rw [hempty, measure_empty]
    exact bot_le
  push_neg at hc1
  set A := c ^ 2 with hAdef
  have hA0 : 0 ≤ A := sq_nonneg c
  have hA1 : A ≤ 1 := by nlinarith
  have hnA : (n : ℝ) * A = (1 + ε) ^ 2 * m := by
    rw [hAdef, hcdef, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  set θ := ε / (8 * (1 + ε)) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ8 : θ ≤ 1 / 8 := by
    rw [hθ, div_le_iff₀ (by positivity)]
    linarith
  set cc : Fin n → ℝ := fun i => θ * (l i - A) with hccdef
  have hcc : ∀ i, |cc i| ≤ 1 / 4 := by
    intro i
    have hla : |l i - A| ≤ 1 := by
      rw [abs_le]; rcases hl01 i with h | h <;> rw [h] <;> constructor <;> linarith
    simp only [hccdef, abs_mul, abs_of_nonneg hθ0]
    nlinarith [abs_nonneg (l i - A)]
  obtain ⟨hint, hle⟩ := rpc0b_gauss_quad b cc hcc
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun v => ∑ i, cc i * (b.repr v i) ^ 2 with hGdef
  have hG : ∀ v, G v = θ * (‖p v‖ ^ 2 - A * ‖v‖ ^ 2) := by
    intro v
    show ∑ i, cc i * (b.repr v i) ^ 2 = _
    rw [(hrep v).1, (hrep v).2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hccdef]
    ring
  have hGc : Continuous G := by
    simp only [hGdef]
    fun_prop
  have hpt : {x : EuclideanSpace ℝ (Fin n) |
      ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Ioi (c * ‖z‖)}
      ⊆ {x | 1 ≤ ENNReal.ofReal (Real.exp (G x))} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_Ioi] at hx ⊢
    rw [ENNReal.one_le_ofReal]
    apply Real.one_le_exp
    rw [hG]
    apply mul_nonneg hθ0
    by_cases hx0 : x = 0
    · simp [hx0]
    · simp only [hx0, if_false, map_smul, norm_smul, norm_div, norm_norm] at hx
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have h1 : c * ‖x‖ < ‖p x‖ := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hxn] at hx
        nlinarith
      have h2 : 0 ≤ c * ‖x‖ := by positivity
      nlinarith
  have hsb : ∑ i, (cc i + 2 * cc i ^ 2) ≤ -(ε ^ 2 * m / 16) := by
    rw [rpc0b_sum_split l hl01 m hsum cc (θ * (1 - A) + 2 * θ ^ 2 * (1 - A) ^ 2)
      (-θ * A + 2 * θ ^ 2 * A ^ 2) (fun i => by rcases hl01 i with h | h <;> simp only [hccdef, h] <;> ring)]
    exact rpc0b_arith_up m n ε A θ hε (Nat.cast_nonneg m) hA0 hA1 hnA hθ
  calc stdGaussian (EuclideanSpace ℝ (Fin n))
        {x | ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Ioi (c * ‖z‖)}
      ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) {x | 1 ≤ ENNReal.ofReal (Real.exp (G x))} := measure_mono hpt
    _ = 1 * stdGaussian (EuclideanSpace ℝ (Fin n)) {x | 1 ≤ ENNReal.ofReal (Real.exp (G x))} := (one_mul _).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (G x)) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) :=
        mul_meas_ge_le_lintegral₀ (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp hGc.measurable)).aemeasurable 1
    _ = ENNReal.ofReal (∫ x, Real.exp (G x) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm
    _ ≤ ENNReal.ofReal (Real.exp (∑ i, (cc i + 2 * cc i ^ 2))) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * m / 16))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hsb)

theorem rpc0b_low_gauss {n : ℕ} (m : ℕ) (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p)
    (hr : Module.finrank ℝ (LinearMap.range (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    stdGaussian (EuclideanSpace ℝ (Fin n))
        {x | ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Iio ((1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)}
      ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * m / 16))) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd (Subsingleton.elim z 0) hz
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨b, l, hl01, hsum, hrep⟩ := rpc0b_eigen m p hi hs hr
  have hmn := rpc0b_m_le_n l hl01 m hsum
  set c := (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) with hcdef
  have hc0 : 0 ≤ c := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  set B := c ^ 2 with hBdef
  have hB0 : 0 ≤ B := sq_nonneg c
  have hmn1 : (m : ℝ) / n ≤ 1 := (div_le_one hnR).2 hmn
  have hnB : (n : ℝ) * B = (1 - ε) ^ 2 * m := by
    rw [hBdef, hcdef, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hB1 : B ≤ 1 := by
    rw [hBdef, hcdef, mul_pow, Real.sq_sqrt (by positivity)]
    have : (1 - ε) ^ 2 ≤ 1 := by nlinarith
    calc (1 - ε) ^ 2 * ((m : ℝ) / n) ≤ 1 * 1 :=
          mul_le_mul this hmn1 (by positivity) zero_le_one
      _ = 1 := by norm_num
  set θ := ε / 8 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  set cc : Fin n → ℝ := fun i => θ * (B - l i) with hccdef
  have hcc : ∀ i, |cc i| ≤ 1 / 4 := by
    intro i
    have hla : |B - l i| ≤ 1 := by
      rw [abs_le]; rcases hl01 i with h | h <;> rw [h] <;> constructor <;> linarith
    simp only [hccdef, abs_mul, abs_of_nonneg hθ0]
    have : θ ≤ 1 / 8 := by rw [hθ]; linarith
    nlinarith [abs_nonneg (B - l i)]
  obtain ⟨hint, hle⟩ := rpc0b_gauss_quad b cc hcc
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun v => ∑ i, cc i * (b.repr v i) ^ 2 with hGdef
  have hG : ∀ v, G v = θ * (B * ‖v‖ ^ 2 - ‖p v‖ ^ 2) := by
    intro v
    show ∑ i, cc i * (b.repr v i) ^ 2 = _
    rw [(hrep v).1, (hrep v).2, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hccdef]
    ring
  have hGc : Continuous G := by
    simp only [hGdef]
    fun_prop
  have hpt : {x : EuclideanSpace ℝ (Fin n) |
      ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Iio (c * ‖z‖)}
      ⊆ {x | 1 ≤ ENNReal.ofReal (Real.exp (G x))} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_Iio] at hx ⊢
    rw [ENNReal.one_le_ofReal]
    apply Real.one_le_exp
    rw [hG]
    apply mul_nonneg hθ0
    by_cases hx0 : x = 0
    · simp [hx0]
    · simp only [hx0, if_false, map_smul, norm_smul, norm_div, norm_norm] at hx
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have h1 : ‖p x‖ < c * ‖x‖ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hxn] at hx
        nlinarith
      have h2 : 0 ≤ ‖p x‖ := norm_nonneg _
      nlinarith
  have hsb : ∑ i, (cc i + 2 * cc i ^ 2) ≤ -(ε ^ 2 * m / 16) := by
    rw [rpc0b_sum_split l hl01 m hsum cc (θ * (B - 1) + 2 * θ ^ 2 * (B - 1) ^ 2)
      (θ * B + 2 * θ ^ 2 * B ^ 2) (fun i => by rcases hl01 i with h | h <;> simp only [hccdef, h] <;> ring)]
    exact rpc0b_arith_low m n ε B θ hε hε1 (Nat.cast_nonneg m) hmn hB0 hB1 hnB hθ
  calc stdGaussian (EuclideanSpace ℝ (Fin n))
        {x | ‖p (if x = 0 then z else (‖z‖ / ‖x‖) • x)‖ ∈ Set.Iio (c * ‖z‖)}
      ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) {x | 1 ≤ ENNReal.ofReal (Real.exp (G x))} := measure_mono hpt
    _ = 1 * stdGaussian (EuclideanSpace ℝ (Fin n)) {x | 1 ≤ ENNReal.ofReal (Real.exp (G x))} := (one_mul _).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (G x)) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) :=
        mul_meas_ge_le_lintegral₀ (ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp hGc.measurable)).aemeasurable 1
    _ = ENNReal.ofReal (∫ x, Real.exp (G x) ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm
    _ ≤ ENNReal.ofReal (Real.exp (∑ i, (cc i + 2 * cc i ^ 2))) := ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 * m / 16))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hsb)

theorem rpc0b_tails {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : HighDimProb.Isoperimetry.IsUniformProjection Prob m P)
    (z : EuclideanSpace ℝ (Fin n)) (ε : ℝ) (hε : 0 < ε) :
    Prob.real {ω | ‖P ω z‖ ∈ Set.Ioi ((1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)}
        ≤ Real.exp (-(ε ^ 2 * m / 16)) ∧
      Prob.real {ω | ‖P ω z‖ ∈ Set.Iio ((1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)}
        ≤ Real.exp (-(ε ^ 2 * m / 16)) := by
  by_cases hz : z = 0
  · subst hz
    simp
    positivity
  constructor
  · rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
      (rpc0b_fubini Prob m P hP _ measurableSet_Ioi z _
        (fun p hi hs hr => rpc0b_up_gauss m p hi hs hr z hz ε hε))
  · by_cases hε1 : ε < 1
    · rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
        (rpc0b_fubini Prob m P hP _ measurableSet_Iio z _
          (fun p hi hs hr => rpc0b_low_gauss m p hi hs hr z hz ε hε hε1))
    · push_neg at hε1
      have hempty : {ω | ‖P ω z‖ ∈ Set.Iio ((1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
        have : (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ 0 := by
          have h1 : 1 - ε ≤ 0 := by linarith
          have h2 : 0 ≤ Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ := by positivity
          nlinarith
        exact this.trans (norm_nonneg _)
      rw [hempty]
      simp
      positivity

open MeasureTheory HighDimProb.Isoperimetry in
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 < ε),
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖ ∧
            ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖} := by
  refine ⟨1 / 16, by norm_num, ?_⟩
  intro Ω _ Prob _ n m P hP z ε hε
  obtain ⟨h1, h2⟩ := rpc0b_tails Prob m P hP z ε hε
  set Up := {ω | ‖P ω z‖ ∈ Set.Ioi ((1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)} with hUp
  set Low := {ω | ‖P ω z‖ ∈ Set.Iio ((1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖)} with hLow
  set Good := {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖ ∧
            ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖} with hGood
  have hcov : (Set.univ : Set Ω) ⊆ Good ∪ (Up ∪ Low) := by
    intro ω _
    simp only [hGood, hUp, hLow, Set.mem_union, Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_Iio]
    by_cases ha : (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖
    · by_cases hb : ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr (Or.inl (lt_of_not_ge hb))
    · exact Or.inr (Or.inr (lt_of_not_ge ha))
  have hle : Prob.real (Set.univ : Set Ω) ≤ Prob.real Good + (Prob.real Up + Prob.real Low) :=
    (measureReal_mono hcov).trans ((measureReal_union_le _ _).trans
      (add_le_add le_rfl (measureReal_union_le _ _)))
  rw [probReal_univ] at hle
  have he : Real.exp (-(1 / 16 * ε ^ 2 * (m : ℝ))) = Real.exp (-(ε ^ 2 * m / 16)) := by ring_nf
  rw [he]
  linarith
