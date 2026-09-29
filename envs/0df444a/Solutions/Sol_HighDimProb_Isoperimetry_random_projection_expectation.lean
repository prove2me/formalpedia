-- Prove2me | solution 1 for HighDimProb.Isoperimetry.random_projection_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T14:10:49.788677+00:00
-- url     : https://prove2.me/submissions/97be6163-9a5c-4e29-be43-b1163f24b0ee

import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

set_option autoImplicit false

open MeasureTheory

theorem rp125_sq_norm_eq_inner {n : ℕ} (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
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

theorem rp125_norm_le {n : ℕ} (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p) (z : EuclideanSpace ℝ (Fin n)) :
    ‖p z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have h1 := rp125_sq_norm_eq_inner p hi hs z
  have h2 : inner ℝ z (p z) ≤ ‖z‖ * ‖p z‖ := real_inner_le_norm _ _
  have h3 : ‖p z‖ ≤ ‖z‖ := by
    rcases (norm_nonneg (p z)).eq_or_lt with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem rp125_sum_sq {n : ℕ} (m : ℕ) (p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hi : IsIdempotentElem p) (hs : IsSelfAdjoint p)
    (hr : Module.finrank ℝ (LinearMap.range (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) = m) :
    ∑ i : Fin n, ‖p (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 = (m : ℝ) := by
  have hil : IsIdempotentElem (p : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
    show _ * _ = _
    refine LinearMap.ext (fun x => ?_)
    have := congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => q x) hi
    simpa using this
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hil).trace
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ), hr] at htr
  rw [← htr]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rp125_sq_norm_eq_inner p hi hs]
  rfl

theorem rp125_invariant {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω)
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : HighDimProb.Isoperimetry.IsUniformProjection Prob m P)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    ∫ ω, ‖P ω (U.symm w)‖ ^ 2 ∂Prob = ∫ ω, ‖P ω w‖ ^ 2 ∂Prob := by
  have hmap := hP.2.2.2.2 U
  set g : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) → ℝ := fun p => ‖p w‖ ^ 2 with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hQ : Measurable (fun ω => (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        ((P ω).comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) := by
    have hc : Continuous (fun p : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        (U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        (p.comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :=
      continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
    exact hc.measurable.comp hP.1
  have e1 := integral_map hQ.aemeasurable hgc.aestronglyMeasurable (μ := Prob)
  have e2 := integral_map hP.1.aemeasurable hgc.aestronglyMeasurable (μ := Prob)
  rw [hmap, e2] at e1
  calc ∫ ω, ‖P ω (U.symm w)‖ ^ 2 ∂Prob
      = ∫ ω, g ((U.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        ((P ω).comp (U.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) ∂Prob := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp [hg]
    _ = ∫ ω, g (P ω) ∂Prob := e1.symm
    _ = ∫ ω, ‖P ω w‖ ^ 2 ∂Prob := rfl

theorem rp125_eq_of_norm_eq {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω)
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : HighDimProb.Isoperimetry.IsUniformProjection Prob m P)
    (u v : EuclideanSpace ℝ (Fin n)) (huv : ‖v‖ = ‖u‖) :
    ∫ ω, ‖P ω u‖ ^ 2 ∂Prob = ∫ ω, ‖P ω v‖ ^ 2 ∂Prob := by
  set U := Submodule.reflection (ℝ ∙ (v - u))ᗮ with hU
  have hUv : U v = u := Submodule.reflection_sub huv
  have := rp125_invariant Prob m P hP U (U v)
  rw [LinearIsometryEquiv.symm_apply_apply, hUv] at this
  exact this.symm

open MeasureTheory HighDimProb.Isoperimetry in
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
    {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∫ ω, ‖P ω z‖ ^ 2 ∂Prob) = Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : z = 0 := Subsingleton.elim _ _
    subst hz
    simp
  set b := EuclideanSpace.basisFun (Fin n) ℝ with hb
  set i0 : Fin n := ⟨0, hn⟩
  have hnorm : ∀ i : Fin n, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hmeas : ∀ x : EuclideanSpace ℝ (Fin n), AEStronglyMeasurable (fun ω => ‖P ω x‖ ^ 2) Prob := by
    intro x
    have : Measurable (fun ω => ‖P ω x‖ ^ 2) := by
      have h1 : Measurable (fun ω => P ω x) := hP.1.apply_continuousLinearMap x
      exact (h1.norm).pow_const 2
    exact this.aestronglyMeasurable
  have hint : ∀ x : EuclideanSpace ℝ (Fin n), Integrable (fun ω => ‖P ω x‖ ^ 2) Prob := by
    intro x
    refine Integrable.of_bound (hmeas x) (‖x‖ ^ 2) ?_
    filter_upwards [hP.2.1, hP.2.2.1] with ω hi hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact rp125_norm_le (P ω) hi hs x
  have hsum : ∑ i : Fin n, ∫ ω, ‖P ω (b i)‖ ^ 2 ∂Prob = (m : ℝ) := by
    rw [← integral_finsetSum _ (fun i _ => hint (b i))]
    have : (fun ω => ∑ i : Fin n, ‖P ω (b i)‖ ^ 2) =ᵐ[Prob] fun _ => (m : ℝ) := by
      filter_upwards [hP.2.1, hP.2.2.1, hP.2.2.2.1] with ω hi hs hr
      exact rp125_sum_sq m (P ω) hi hs hr
    rw [integral_congr_ae this]
    simp
  have heach : ∀ i : Fin n, ∫ ω, ‖P ω (b i)‖ ^ 2 ∂Prob = ∫ ω, ‖P ω (b i0)‖ ^ 2 ∂Prob :=
    fun i => rp125_eq_of_norm_eq Prob m P hP (b i) (b i0) (by rw [hnorm, hnorm])
  have hf0 : ∫ ω, ‖P ω (b i0)‖ ^ 2 ∂Prob = (m : ℝ) / n := by
    rw [Finset.sum_congr rfl (fun i _ => heach i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    linarith
  have hz : ∫ ω, ‖P ω z‖ ^ 2 ∂Prob = (m : ℝ) / n * ‖z‖ ^ 2 := by
    rw [rp125_eq_of_norm_eq Prob m P hP z (‖z‖ • b i0) (by rw [norm_smul, hnorm, mul_one, norm_norm])]
    simp only [map_smul, norm_smul, norm_norm, mul_pow]
    rw [integral_const_mul, hf0]
    ring
  rw [hz, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
