-- Prove2me | solution 1 for OAI.SKGap.positive_time_root_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:20.070218+00:00
-- url     : https://prove2.me/submissions/880fd2c0-5fb0-4d26-a9c9-353438d31ced

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_conditional_bad_integral_rate
import Theorems.Thm_OAI_SKGap_field_logdet_uniform

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_KernelDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
variable {ι κ : Type*} [Fintype κ]

theorem additive_noise_lintegral (μ : Measure (ι → ℝ)) [SFinite μ]
    (φ : (κ → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (L : (ι → ℝ) → (κ → ℝ)) (hL : Measurable L)
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1,L z.1+z.2) ∂μ.prod ((volume : Measure (κ → ℝ)).withDensity φ)) =
      ∫⁻ y, ∫⁻ x, φ (y-L x)*F (x,y) ∂μ ∂volume := by
  rw [lintegral_prod _ (by fun_prop)]
  have he (x : ι → ℝ) :
      (∫⁻ e, F (x,L x+e) ∂(volume : Measure (κ → ℝ)).withDensity φ)=
      ∫⁻ y, φ (y-L x)*F (x,y) ∂volume := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hφ (by fun_prop)]
    have hh := lintegral_add_left_eq_self
      (μ := (volume : Measure (κ → ℝ))) (fun y => φ (y-L x)*F (x,y)) (L x)
    simpa only [Pi.mul_apply,add_sub_cancel_left] using hh
  simp only [he]
  exact lintegral_lintegral_swap (by fun_prop)

theorem residual_density_lintegral (ρ : Measure (ι → ℝ)) [SFinite ρ]
    (p : (κ → ℝ) → ℝ≥0∞) (hp : Measurable p)
    (K : (κ → ℝ) → (ι → ℝ)) (hK : Measurable K)
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1+K z.2,z.2) ∂ρ.prod ((volume : Measure (κ → ℝ)).withDensity p)) =
      ∫⁻ y, p y*(∫⁻ r, F (r+K y,y) ∂ρ) ∂volume := by
  rw [lintegral_prod_symm _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop)]
  rfl

theorem kernel_test_ae (μ ρ : Measure (ι → ℝ)) [SFinite μ] [SFinite ρ]
    {φ p : (κ → ℝ) → ℝ≥0∞} (hφ : Measurable φ) (hp : Measurable p)
    {L : (ι → ℝ) → (κ → ℝ)} {K : (κ → ℝ) → (ι → ℝ)}
    (hL : Measurable L) (hK : Measurable K)
    (hjoint : (μ.prod ((volume : Measure (κ → ℝ)).withDensity φ)).map
      (fun z => (z.1,L z.1+z.2)) =
      (ρ.prod ((volume : Measure (κ → ℝ)).withDensity p)).map
        (fun z => (z.1+K z.2,z.2)))
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ)=ᵐ[volume]
      (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) := by
  have h1 : Measurable (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ) := by fun_prop
  have h2 : Measurable (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) := by fun_prop
  apply (withDensity_eq_iff_of_sigmaFinite h1.aemeasurable h2.aemeasurable).mp
  ext s hs
  rw [withDensity_apply _ hs,withDensity_apply _ hs]
  let F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞ := fun z => s.indicator (fun _ => f z.1) z.2
  have hF : Measurable F := by
    exact (hf.comp measurable_fst).indicator (hs.preimage measurable_snd)
  have hh := congrArg (fun ν => ∫⁻ z, F z ∂ν) hjoint
  rw [lintegral_map hF (by fun_prop),lintegral_map hF (by fun_prop),
    additive_noise_lintegral μ φ hφ L hL F hF,
    residual_density_lintegral ρ p hp K hK F hF] at hh
  have he1 (y : κ → ℝ) : (∫⁻ x, φ (y-L x)*F (x,y) ∂μ)=
      s.indicator (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ) y := by
    by_cases hy : y ∈ s <;> simp [F,hy]
  have he2 (y : κ → ℝ) : p y*(∫⁻ r, F (r+K y,y) ∂ρ)=
      s.indicator (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) y := by
    by_cases hy : y ∈ s <;> simp [F,hy]
  simp_rw [he1,he2] at hh
  simpa only [lintegral_indicator hs] using hh

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_ContinuousKernel
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma integrable_bounded (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)

theorem continuous_kernel_posterior (μ ρ : Measure (ι → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {φ p : (κ → ℝ) → ℝ} (hφ : Continuous φ) (hp : Continuous p)
    (hφpos : ∀ y,0 ≤ φ y) (hppos : ∀ y,0 ≤ p y)
    {C : ℝ} (hC : 0 ≤ C) (hφC : ∀ y,φ y ≤ C)
    {L : (ι → ℝ) → (κ → ℝ)} {K : (κ → ℝ) → (ι → ℝ)}
    (hL : Continuous L) (hK : Continuous K)
    (hjoint : (μ.prod ((volume : Measure (κ → ℝ)).withDensity (fun y => ENNReal.ofReal (φ y)))).map
      (fun z => (z.1,L z.1+z.2)) =
      (ρ.prod ((volume : Measure (κ → ℝ)).withDensity (fun y => ENNReal.ofReal (p y)))).map
        (fun z => (z.1+K z.2,z.2))) (z : κ → ℝ) :
    μ.withDensity (fun x => ENNReal.ofReal (φ (z-L x))) =
      ENNReal.ofReal (p z) • ρ.map (fun r => r+K z) := by
  have hiφ (y : κ → ℝ) : Integrable (fun x => φ (y-L x)) μ :=
    integrable_bounded μ (by fun_prop) (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
  have := isFiniteMeasure_withDensity_ofReal (hiφ z).hasFiniteIntegral
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  let fr : (ι → ℝ) →ᵇ ℝ := ⟨⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
    f.map_bounded'⟩
  have hfr (x : ι → ℝ) : 0 ≤ fr x := (f x).coe_nonneg
  have hb (x : ι → ℝ) : ‖fr x‖ ≤ ‖fr‖ := fr.norm_coe_le_norm x
  have hi1 (y : κ → ℝ) : Integrable (fun x => φ (y-L x)*fr x) μ := by
    apply integrable_bounded μ (by fun_prop) (C := C*‖fr‖)
    intro x
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφpos _)]
    exact mul_le_mul (hφC _) (hb x) (norm_nonneg _) hC
  have hi2 (y : κ → ℝ) : Integrable (fun r => fr (r+K y)) ρ :=
    integrable_bounded ρ (by fun_prop) (fun r => hb _)
  have hc1 : Continuous (fun y => ∫ x, φ (y-L x)*fr x ∂μ) := by
    apply continuous_of_dominated (bound := fun _ => C*‖fr‖)
    · intro y; exact (hi1 y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun x => by
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφpos _)]
        exact mul_le_mul (hφC _) (hb x) (norm_nonneg _) hC)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun x => by fun_prop)
  have hc2 : Continuous (fun y => ∫ r, fr (r+K y) ∂ρ) := by
    apply continuous_of_dominated (bound := fun _ => ‖fr‖)
    · intro y; exact (hi2 y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun r => hb _)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun r => by fun_prop)
  have he1 (y : κ → ℝ) :
      (∫⁻ x, ENNReal.ofReal (φ (y-L x))*(f x : ℝ≥0∞) ∂μ)=
      ENNReal.ofReal (∫ x, φ (y-L x)*fr x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi1 y) (Filter.Eventually.of_forall (fun x => mul_nonneg (hφpos _) (hfr x)))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (hφpos _)]
    change _ * (f x : ℝ≥0∞) = _ * ENNReal.ofReal (f x : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have he2 (y : κ → ℝ) :
      ENNReal.ofReal (p y)*(∫⁻ r, (f (r+K y) : ℝ≥0∞) ∂ρ)=
      ENNReal.ofReal (p y*(∫ r, fr (r+K y) ∂ρ)) := by
    rw [ENNReal.ofReal_mul (hppos y),ofReal_integral_eq_lintegral_ofReal (hi2 y)
      (Filter.Eventually.of_forall (fun r => hfr _))]
    congr 1
    apply lintegral_congr
    intro r
    change (f (r+K y) : ℝ≥0∞) = ENNReal.ofReal (f (r+K y) : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have hae := kernel_test_ae μ ρ hφ.measurable.ennreal_ofReal hp.measurable.ennreal_ofReal
    hL.measurable hK.measurable hjoint (fun x => (f x : ℝ≥0∞)) (by fun_prop)
  simp only [he1,he2] at hae
  have hall := (Continuous.ae_eq_iff_eq (volume : Measure (κ → ℝ))
    (ENNReal.continuous_ofReal.comp hc1) (ENNReal.continuous_ofReal.comp (hp.mul hc2))).mp hae
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_smul_measure,lintegral_map (by fun_prop) (by fun_prop)]
  change (∫⁻ x, ENNReal.ofReal (φ (z-L x))*(f x : ℝ≥0∞) ∂μ)=
    ENNReal.ofReal (p z)*(∫⁻ r, (f (r+K z) : ℝ≥0∞) ∂ρ)
  rw [he1,he2]
  exact congrFun hall z

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma empiricalLaw_coe (y : ι → ℝ) : (empiricalLaw y : Measure ℝ) =
    (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i) := rfl

lemma integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (y i) := by
  rw [empiricalLaw_coe, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableFields
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

theorem overlap_nonneg {n : ℕ} (y : Field n) : 0 ≤ overlap y :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)

theorem overlap_lt_one {n : ℕ} (hn : 0 < n) (y : Field n) : overlap y < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_lt_iff₀ hn').mpr
  simp only [one_mul]
  calc
    (∑ i, magnetization y i ^ 2) < ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
      · intro i _
        exact tanh_sq_lt_one (y i)
    _ = n := by simp

theorem vectorSqNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorSqNorm x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem hessian_quadratic_formula {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (y A x : Field n) :
    quadraticForm (fieldHessian j J y A) x = vectorSqNorm x +
      onsager j y * vectorSqNorm (fun i => sqrt (A i) * x i) -
      quadraticForm J (fun i => sqrt (A i) * x i) -
      (2 * j / n) * (∑ i, magnetization y i * (sqrt (A i) * x i)) ^ 2 := by
  have hi (i : Fin n) :
      (∑ k, x i * fieldHessian j J y A i k * x k) = x i ^ 2 +
        onsager j y * (sqrt (A i) * x i) ^ 2 -
        (∑ k, (sqrt (A i) * x i) * J i k * (sqrt (A k) * x k)) -
        (2 * j / n) * (magnetization y i * (sqrt (A i) * x i)) *
          (∑ k, magnetization y k * (sqrt (A k) * x k)) := by
    calc
      _ = ∑ k, ((if i = k then x i ^ 2 else 0) +
          (if i = k then onsager j y * (sqrt (A i) * x i) ^ 2 else 0) -
          (sqrt (A i) * x i) * J i k * (sqrt (A k) * x k) -
          (2 * j / n) * (magnetization y i * (sqrt (A i) * x i)) *
            (magnetization y k * (sqrt (A k) * x k))) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : i = k
        · subst k
          simp only [fieldHessian, hessianCore, ↓reduceIte]
          ring
        · simp only [fieldHessian, hessianCore, ite_eq_right hk]
          ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  unfold quadraticForm
  simp_rw [hi]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, vectorSqNorm]
  ring

theorem magnetization_hasFDerivAt {n : ℕ} (y : Field n) (i : Fin n) :
    HasFDerivAt (fun z : Field n => magnetization z i)
      (spinVariance y i • (ContinuousLinearMap.proj i : Field n →L[ℝ] ℝ)) y :=
  (hasDerivAt_tanh (y i)).comp_hasFDerivAt y (hasFDerivAt_apply i y)

theorem overlap_hasFDerivAt {n : ℕ} (y : Field n) :
    HasFDerivAt overlap (overlapDerivative y) y := by
  have hd := (HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).pow 2)).const_mul (n : ℝ)⁻¹
  convert! hd using 1
  · ext z
    simp only [overlap, Finset.sum_apply, div_eq_mul_inv]
    ring
  · ext v
    simp only [overlapDerivative, _root_.smul_apply,
      _root_.sum_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      nsmul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

theorem onsager_hasFDerivAt {n : ℕ} (j : ℝ) (y : Field n) :
    HasFDerivAt (onsager j) (-j • overlapDerivative y) y := by
  convert! ((overlap_hasFDerivAt y).const_sub 1).const_mul j using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  simp only [_root_.smul_apply, smul_eq_mul, _root_.neg_apply]
  ring

theorem tapField_hasFDerivAt {n : ℕ} (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    HasFDerivAt (tapField j J h)
      ((fieldJacobian j J y).mulVecLin.toContinuousLinearMap) y := by
  rw [hasFDerivAt_pi']
  intro i
  have hfirst := ((hasFDerivAt_apply i y).sub_const (h i)).add
    ((onsager_hasFDerivAt j y).mul (magnetization_hasFDerivAt y i))
  have hlast := HasFDerivAt.sum (u := Finset.univ)
    (fun k _ => (magnetization_hasFDerivAt y k).const_mul (J i k))
  convert! hfirst.sub hlast using 1
  · ext z
    simp only [tapField, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, fieldJacobian, hessianCore, _root_.sub_apply,
      _root_.add_apply, _root_.smul_apply,
      _root_.sum_apply, smul_eq_mul, overlapDerivative]
    have hdelta : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) = v i := by
      simp
    have hdeltaV : (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
        spinVariance y k * v k) = spinVariance y i * v i := by simp
    calc
      _ = (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) * v k) +
          onsager j y * (∑ k : Fin n, (if i = k then 1 else (0 : ℝ)) *
            spinVariance y k * v k) -
          (∑ k, J i k * (spinVariance y k * v k)) -
          (2 * j / n) * magnetization y i *
            (∑ k, (magnetization y k * spinVariance y k) * v k) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        rw [hdelta, hdeltaV]
        ring

theorem vectorNorm_nonneg {n : ℕ} (x : Field n) : 0 ≤ vectorNorm x := norm_nonneg _

theorem vectorNorm_sq {n : ℕ} (x : Field n) : vectorNorm x ^ 2 = vectorSqNorm x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

theorem vectorNorm_add_le {n : ℕ} (x z : Field n) :
    vectorNorm (x + z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_sub_le {n : ℕ} (x z : Field n) :
    vectorNorm (x - z) ≤ vectorNorm x + vectorNorm z := by
  exact norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

theorem vectorNorm_smul {n : ℕ} (a : ℝ) (x : Field n) :
    vectorNorm (fun i => a * x i) = |a| * vectorNorm x := by
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))

theorem vector_dot_abs_le {n : ℕ} (x z : Field n) :
    |∑ i, x i * z i| ≤ vectorNorm x * vectorNorm z := by
  simpa only [vectorNorm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply, mul_comm] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 z)

attribute [local irreducible] vectorNorm

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarParametersJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma scalarQMoment_bounds (P : ProbabilityMeasure ℝ) : 0 ≤ scalarQMoment P ∧ scalarQMoment P ≤ 1 := by
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hi : Integrable (fun x : ℝ => tanh x^2) (P : Measure ℝ) := Integrable.of_bound
    (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le))
  have h := integral_mono hi (integrable_const (1:ℝ)) (fun x => (tanh_sq_lt_one x).le)
  simpa only [scalarQMoment, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ProductGaussianDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace SKGap.GaussianDensity
variable {ι : Type*} [Fintype ι]

theorem pi_gaussian_density (m : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i,v i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (v i)) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal (m i) (v i) (x i))
      (volume.restrict (Set.univ.pi s)) := by
    exact (Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (m i) (v i))).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  change ENNReal.ofReal (∫ x, (∏ i,gaussianPDFReal (m i) (v i) (x i))
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s))=_
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero _ (hv i),withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal (m i) (v i)).restrict
    (Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _))

lemma measurable_productPDF (m : ι → ℝ) (v : ι → ℝ≥0) :
    Measurable (fun x : ι → ℝ => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  fun_prop

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EqualityCurve
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianDensity

lemma map_withDensity_leftInverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) (d : α → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity d).map f=(μ.map f).withDensity (d ∘ g) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs,
    setLIntegral_map hs (hd.comp hg) hf]
  apply lintegral_congr
  intro x
  simp only [Function.comp_apply]
  rw [hgf x]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_map_gaussian_density (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => A*ᵥx) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
        (|A.det⁻¹| *∏ i,gaussianPDFReal 0 1 ((A⁻¹*ᵥx) i))) := by
  have hm (B : Matrix ι ι ℝ) : Measurable (fun x => B*ᵥx) := by fun_prop
  have hleft : Function.LeftInverse (fun x => A⁻¹*ᵥx) (fun x => A*ᵥx) := by
    intro x
    change A⁻¹*ᵥ(A*ᵥx)=x
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec]
  rw [pi_gaussian_density (fun _ : ι => 0) (fun _ => 1) (fun _ => one_ne_zero),
    map_withDensity_leftInverse _ (hm A) (hm A⁻¹) hleft _ (measurable_productPDF _ _)]
  have hvol : (volume : Measure (ι → ℝ)).map (fun x => A*ᵥx)=
      ENNReal.ofReal |A.det⁻¹| • volume := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  rw [hvol,withDensity_smul_measure,← withDensity_smul _ ((measurable_productPDF _ _).comp (hm A⁻¹))]
  congr 1
  ext x
  simp only [Pi.smul_apply,Function.comp_apply,smul_eq_mul,ENNReal.ofReal_mul (abs_nonneg _)]

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

theorem law_eq_of_mean_covariance {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hm : ∀ i, (∫ w, X w i ∂P) = ∫ w, Y w i ∂P')
    (hc : ∀ i k, cov[fun w => X w i, fun w => X w k; P] =
      cov[fun w => Y w i, fun w => Y w k; P']) :
    P.map X = P'.map Y := by
  classical
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  apply Measure.ext_of_charFunDual
  ext L
  rw [hX.charFunDual_map_eq,hY.charFunDual_map_eq]
  let c : ι → ℝ := fun i => L (fun k => if i=k then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, x i * c i := by
    simpa only [c, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x
  have hLX : L ∘ X = fun w => ∑ i, X w i*c i := funext (fun w => hL (X w))
  have hLY : L ∘ Y = fun w => ∑ i, Y w i*c i := funext (fun w => hL (Y w))
  have hiX (i : ι) := (hX.eval i).memLp_two
  have hiY (i : ι) := (hY.eval i).memLp_two
  have hem : (∫ w, (L ∘ X) w ∂P) = ∫ w, (L ∘ Y) w ∂P' := by
    rw [hLX,hLY]
    rw [integral_finsetSum _ (fun i _ => ((hX.eval i).integrable.mul_const _)),
      integral_finsetSum _ (fun i _ => ((hY.eval i).integrable.mul_const _))]
    simp only [integral_mul_const,hm]
  have hev : Var[L ∘ X; P] = Var[L ∘ Y; P'] := by
    rw [← covariance_self (hX.map L).aemeasurable,
      ← covariance_self (hY.map L).aemeasurable]
    rw [hLX,hLY]
    rw [covariance_fun_sum_fun_sum (fun i => (hiX i).mul_const _) (fun i => (hiX i).mul_const _),
      covariance_fun_sum_fun_sum (fun i => (hiY i).mul_const _) (fun i => (hiY i).mul_const _)]
    simp only [covariance_mul_const_left,covariance_mul_const_right,hc]
  rw [hev,hem]

theorem residual_independent {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    IndepFun (fun w => X w-K*ᵥ Y w) Y P := by
  have := hXY.isProbabilityMeasure
  have hR : HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P := by
    exact hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
      (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))
  apply hR.indepFun_of_covariance_eval
  intro i k
  change cov[fun w => X w i-∑ l, K i l*Y w l,fun w => Y w k; P]=0
  have hK : MemLp (fun w => ∑ l, K i l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval i).memLp_two
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two hK (hXY.snd.eval k).memLp_two]
  rw [covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _)
    (hXY.snd.eval k).memLp_two]
  simp only [covariance_const_mul_left,hcov,sub_self]

end SKGap.GaussianRegression
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma coordinates_gaussian {κ : Type*} [Fintype κ] :
    HasGaussianLaw (fun g : κ → ℝ => g) (gaussianCoordinates κ) :=
  (iIndepFun_pi (fun _ : κ => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (i k : κ) :
    cov[fun g : κ → ℝ => g i,fun g : κ → ℝ => g k;gaussianCoordinates κ] =
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [ite_eq_left rfl,covariance_self (measurable_pi_apply i).aemeasurable,
      (coordinate_hasLaw i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ : κ => aemeasurable_id)).indepFun h).covariance_eq_zero
      (coordinate_hasLaw i).hasGaussianLaw.memLp_two (coordinate_hasLaw k).hasGaussianLaw.memLp_two

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

lemma linear_gaussian_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : κ → ℝ) :
    cov[fun g => ∑ i, a i*g i,fun g => ∑ i, b i*g i;gaussianCoordinates κ] =
      ∑ i, a i*b i := by
  rw [covariance_fun_sum_fun_sum
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance]
  simp [mul_comm]

lemma matrix_sample_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    HasGaussianLaw (fun g => A*ᵥg) (gaussianCoordinates κ) :=
  coordinates_gaussian.map_fun (GaussianRegression.matrixCLM A)

lemma matrix_sample_covariance {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (i k : ι) :
    cov[fun g => (A*ᵥg) i,fun g => (A*ᵥg) k;gaussianCoordinates κ] = (A*Aᵀ) i k :=
  linear_gaussian_covariance (A i) (A k)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianDisintegration
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

lemma residual_joint_gaussian {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ) :
    HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P :=
  hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
    (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))

theorem regression_joint_law {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    P.map (fun w => (X w,Y w)) =
      ((P.map (fun w => X w-K*ᵥ Y w)).prod (P.map Y)).map
        (fun z : (ι → ℝ) × (κ → ℝ) => (z.1+K*ᵥ z.2,z.2)) := by
  have := hXY.isProbabilityMeasure
  have hR := residual_joint_gaussian hXY K
  have hi := residual_independent hXY K hcov
  rw [← hi.map_prod_eq_prod_map_map hR.fst.aemeasurable hR.snd.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hR.aemeasurable]
  congr 1
  funext w
  simp only [Function.comp_apply,sub_add_cancel]

end SKGap.GaussianRegression
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RankCovariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rankOneCovarianceInverse_mul (s r : ℝ) (m : ι → ℝ)
    (hs : s ≠ 0) (hS : s+r*(m⬝ᵥm) ≠ 0) :
    rankOneCovarianceInverse s r m * rankOneCovariance s r m=1 := by
  simp only [rankOneCovarianceInverse,rankOneCovariance,Matrix.sub_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    Matrix.vecMulVec_mul_vecMulVec]
  ext i k
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,Pi.smul_apply]
  field_simp [hs,hS]
  ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rankOneCovariance_det {s : ℝ} (hs : s ≠ 0) (r : ℝ) (m : ι → ℝ) :
    (rankOneCovariance s r m).det=s^(Fintype.card ι)*(1+(r/s)*(m⬝ᵥm)) := by
  have he : rankOneCovariance s r m=s • (1+vecMulVec ((r/s) • m) m) := by
    ext i k
    simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.vecMulVec_apply,Pi.smul_apply]
    field_simp
  rw [he,Matrix.det_smul,Matrix.vecMulVec_eq Unit,Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct_smul,smul_eq_mul]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma rankOneTransform_transpose (a b : ℝ) (u : ι → ℝ) :
    (rankOneTransform a b u)ᵀ=rankOneTransform a b u := by
  ext i k
  simp [rankOneTransform,Matrix.one_apply,Matrix.vecMulVec_apply,eq_comm,mul_comm]

lemma rankOneTransform_mul {u : ι → ℝ} (hu : u⬝ᵥu=1) (a b c d : ℝ) :
    rankOneTransform a b u *rankOneTransform c d u =rankOneTransform (a*c) (b*d) u := by
  simp only [rankOneTransform,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,Matrix.vecMulVec_mul_vecMulVec,hu]
  ext i k
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Pi.smul_apply]
  ring

lemma rankOneTransform_det {a : ℝ} (ha : a ≠ 0) (b : ℝ) {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (rankOneTransform a b u).det=a^(Fintype.card ι)*(b/a) := by
  have he : rankOneTransform a b u=rankOneCovariance a (b-a) u := rfl
  rw [he,rankOneCovariance_det ha,hu,mul_one]
  congr 1
  field_simp
  ring

lemma rankOneTransform_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (rankOneTransform a b u)⁻¹=rankOneTransform a⁻¹ b⁻¹ u := by
  apply Matrix.inv_eq_left_inv
  rw [rankOneTransform_mul hu,inv_mul_cancel₀ ha,inv_mul_cancel₀ hb]
  simp [rankOneTransform]

lemma rankOneTransform_mulVec (a b : ℝ) (u x : ι → ℝ) :
    rankOneTransform a b u*ᵥx=a • x+((b-a)*(u⬝ᵥx)) • u := by
  ext i
  simp only [rankOneTransform,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul,op_smul_eq_smul]
  ring

lemma rankOneTransform_norm_sq {u : ι → ℝ} (hu : u⬝ᵥu=1) (a b : ℝ) (x : ι → ℝ) :
    (rankOneTransform a b u*ᵥx)⬝ᵥ(rankOneTransform a b u*ᵥx)=
      a^2*(x⬝ᵥx)+(b^2-a^2)*(u⬝ᵥx)^2 := by
  rw [rankOneTransform_mulVec]
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,hu]
  rw [dotProduct_comm x u]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianLinearDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

theorem gaussian_density_of_matrix (hX : HasGaussianLaw X P) (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=(A*Aᵀ) i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
      (|A.det⁻¹| *∏ i,gaussianPDFReal 0 1 ((A⁻¹*ᵥx) i))) := by
  have hl : P.map X=(gaussianCoordinates ι).map (fun x => A*ᵥx) := by
    apply GaussianRegression.law_eq_of_mean_covariance hX (matrix_sample_gaussian A)
    · intro i
      rw [hm]
      exact (linear_gaussian_mean (A i)).symm
    · intro i k
      rw [hc,matrix_sample_covariance]
  rw [hl]
  exact matrix_map_gaussian_density A hA

lemma gaussian_rankOne_density (hX : HasGaussianLaw X P) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      rankOneTransform (a^2) (b^2) u i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
      ((a^(Fintype.card ι)*(b/a))⁻¹*∏ i,gaussianPDFReal 0 1
        ((rankOneTransform a⁻¹ b⁻¹ u*ᵥx) i))) := by
  have hd : 0 < (rankOneTransform a b u).det := by
    rw [rankOneTransform_det ha.ne' b hu]
    positivity
  have hc' : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      (rankOneTransform a b u*(rankOneTransform a b u)ᵀ) i k := by
    intro i k
    rw [hc,rankOneTransform_transpose,rankOneTransform_mul hu]
    simp only [← pow_two]
  rw [gaussian_density_of_matrix hX _ hd.ne' hm hc',
    rankOneTransform_inv ha.ne' hb.ne' hu,abs_of_pos (inv_pos.mpr hd),rankOneTransform_det ha.ne' b hu]

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma product_gaussianPDF_formula (v : ℝ≥0) (x : ι → ℝ) :
    (∏ i,gaussianPDFReal 0 v (x i))=(sqrt (2*Real.pi*v))⁻¹^(Fintype.card ι)*
      exp (-(x⬝ᵥx)/(2*v)) := by
  simp only [gaussianPDFReal,sub_zero,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,← exp_sum,← Finset.sum_div,← Finset.sum_neg_distrib,dotProduct,← pow_two]

omit [DecidableEq ι] in
lemma product_gaussianPDF_radial {a : ℝ} (ha : 0 ≤ a) (x : ι → ℝ) :
    (∏ i,gaussianPDFReal 0 (NNReal.mk (a^2) (sq_nonneg a)) (x i))=radialDensity a x := by
  rw [product_gaussianPDF_formula]
  simp only [NNReal.coe_mk,radialDensity,sqrt_mul (by positivity : 0 ≤ 2*Real.pi),sqrt_sq ha]

lemma rankOne_density_radial {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (x : ι → ℝ) :
    (a^(Fintype.card ι)*(b/a))⁻¹*(∏ i,gaussianPDFReal 0 1
      ((rankOneTransform a⁻¹ b⁻¹ u*ᵥx) i)) =
    (a/b)*radialDensity a x*exp ((b^2-a^2)/(2*a^2*b^2)*(u⬝ᵥx)^2) := by
  rw [product_gaussianPDF_formula,rankOneTransform_norm_sq hu]
  simp only [NNReal.coe_one,mul_one]
  have he : -(a⁻¹^2*(x⬝ᵥx)+(b⁻¹^2-a⁻¹^2)*(u⬝ᵥx)^2)/2 =
      -(x⬝ᵥx)/(2*a^2)+(b^2-a^2)/(2*a^2*b^2)*(u⬝ᵥx)^2 := by
    field_simp
    ring
  rw [he,exp_add]
  unfold radialDensity
  have hc : (a^(Fintype.card ι)*(b/a))⁻¹*(sqrt (2*Real.pi))⁻¹^(Fintype.card ι)=
      (a/b)*((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι) := by
    simp only [_root_.mul_inv_rev,mul_pow,inv_pow,inv_inv,div_eq_mul_inv]
    ring
  rw [← mul_assoc,← mul_assoc,hc]
  ring

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

omit [Fintype ι] in
lemma rankOne_scaled_covariance (s r c : ℝ) (u : ι → ℝ) :
    rankOneCovariance s r (c • u)=rankOneTransform s (s+r*c^2) u := by
  ext i k
  simp only [rankOneCovariance,rankOneTransform,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.vecMulVec_apply,Pi.smul_apply]
  ring

lemma scaled_unit_exists [Nonempty ι] (m : ι → ℝ) :
    ∃ (c : ℝ) (u : ι → ℝ), 0 ≤ c ∧ u⬝ᵥu=1 ∧ m=c • u := by
  by_cases hm : m=0
  · let i : ι := Classical.choice inferInstance
    refine ⟨0,Pi.single i 1,le_rfl,?_,by simp [hm]⟩
    simp [dotProduct,Pi.single_apply]
  · have hq : 0 < m⬝ᵥm := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i)))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hm))
    have hc : 0 < sqrt (m⬝ᵥm) := sqrt_pos.mpr hq
    refine ⟨sqrt (m⬝ᵥm),(sqrt (m⬝ᵥm))⁻¹ • m,hc.le,?_,?_⟩
    · simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
      have hh := sq_sqrt hq.le
      field_simp
      nlinarith
    · simp [smul_smul,hc.ne']

theorem gaussian_rankOne_covariance_density [Nonempty ι]
    (hX : HasGaussianLaw X P) {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (m : ι → ℝ) (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=rankOneCovariance s r m i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (rankOneDensity s r m x)) := by
  obtain ⟨c,u,hcpos,hu,rfl⟩ := scaled_unit_exists m
  have hS : 0 < s+r*c^2 := add_pos_of_pos_of_nonneg hs (mul_nonneg hr (sq_nonneg c))
  have ha : 0 < sqrt s := sqrt_pos.mpr hs
  have hb : 0 < sqrt (s+r*c^2) := sqrt_pos.mpr hS
  have hc' : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      rankOneTransform ((sqrt s)^2) ((sqrt (s+r*c^2))^2) u i k := by
    intro i k
    rw [sq_sqrt hs.le,sq_sqrt hS.le,hc,rankOne_scaled_covariance]
  rw [gaussian_rankOne_density hX ha hb hu hm hc']
  congr 1
  ext x
  rw [rankOne_density_radial ha.ne' hb.ne' hu x]
  simp only [rankOneDensity,smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,
    sq_sqrt hs.le,sq_sqrt hS.le]
  have hq : c*c=c^2 := by ring
  rw [hq]
  have hpref : sqrt s/sqrt (s+r*c^2)=sqrt (s/(s+r*c^2)) := (sqrt_div hs.le _).symm
  rw [hpref]
  congr 2
  congr 1
  field_simp
  ring

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap

variable {ι : Type*}

variable [Fintype ι]

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

lemma goeMatrix_pi_lipschitz (r : ℝ) :
    LipschitzWith (⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
      (goeMatrix (ι := ι) r) := by
  exact (goeMatrix_L2_lipschitz (ι := ι) r).comp
    (PiLp.lipschitzWith_toLp 2 (fun _ : MatrixCoordinates ι => ℝ))

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEGaussian
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goeEntryCoeff_sample (r : ℝ) (g : MatrixCoordinates ι → ℝ) (i k : ι) :
    (goeEntryCoeff r*ᵥg) (i,k) = goeMatrix r g i k := by
  simp only [mulVec,dotProduct,goeEntryCoeff,mul_assoc,add_mul]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp [goeMatrix]

lemma goe_matrix_gaussian (r : ℝ) :
    HasGaussianLaw (fun (g : MatrixCoordinates ι → ℝ) (p : ι × ι) => goeMatrix r g p.1 p.2) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := matrix_sample_gaussian (goeEntryCoeff (ι := ι) r)
  simpa only [show (fun g => goeEntryCoeff (ι := ι) r*ᵥg) =
    (fun g p => goeMatrix r g p.1 p.2) from funext (fun g => funext (fun p => goeEntryCoeff_sample r g p.1 p.2))] using hh

lemma goe_entry_cov {r : ℝ} (hr : 0 ≤ r) (i k l m : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l m;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=m then 1 else 0)+
       (if i=m then 1 else 0)*(if k=l then 1 else 0)) := by
  let μ := gaussianCoordinates (MatrixCoordinates ι)
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => sqrt (2*r)/2*(g (.inl (l,m))+g (.inl (m,l))); μ]=_
  rw [covariance_const_mul_left,covariance_const_mul_right]
  change sqrt (2*r)/2*(sqrt (2*r)/2*cov[(fun g => g (.inl (i,k))) + (fun g => g (.inl (k,i))),
    (fun g => g (.inl (l,m))) + (fun g => g (.inl (m,l)));gaussianCoordinates (MatrixCoordinates ι)]) = _
  rw [covariance_add_left (hm _) (hm _) ((hm _).add (hm _)),
    covariance_add_right (hm _) (hm _) (hm _),
    covariance_add_right (hm _) (hm _) (hm _)]
  simp only [coordinate_covariance,Sum.inl.injEq,Prod.mk.injEq]
  have hs : (sqrt (2*r)/2)^2=r/2 := by rw [div_pow,sq_sqrt (by positivity)]; ring
  have hs' : sqrt (2*r)/2*(sqrt (2*r)/2)=r/2 := by nlinarith only [hs]
  rw [← mul_assoc,hs']
  have hind (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1:ℝ) else 0)=(if p then 1 else 0)*(if q then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hind]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEObservation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma observationCoeff_sample (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    observationCoeff r v m*ᵥg=goeObservation r v m g := by
  ext i
  change (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ k, goeMatrix r g i k*m k)+sqrt v*g (.inr i)
  rw [show (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ a, (∑ k, m k*goeEntryCoeff r (i,k) a)*g a)+sqrt v*g (.inr i) by
      simp [add_mul,Finset.sum_add_distrib]]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hh := goeEntryCoeff_sample r g i k
  change (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=goeMatrix r g i k*m k
  rw [show (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=m k*((goeEntryCoeff r*ᵥg) (i,k)) by
    simp only [mulVec,dotProduct,Finset.mul_sum,mul_assoc]]
  rw [hh,mul_comm]

lemma goe_observation_joint_gaussian (r v : ℝ) (m : ι → ℝ) :
    HasGaussianLaw (fun g => ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := coordinates_gaussian.map_fun
    ((GaussianRegression.matrixCLM (goeEntryCoeff (ι := ι) r)).prod
      (GaussianRegression.matrixCLM (observationCoeff r v m)))
  apply hh.congr
  filter_upwards [] with g
  simp only [ContinuousLinearMap.prod_apply,GaussianRegression.matrixCLM_apply,
    observationCoeff_sample]
  congr 1
  funext p
  exact goeEntryCoeff_sample r g p.1 p.2

lemma goe_noise_cov (r : ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_const_mul_left]
  change sqrt (2*r)/2*cov[(fun g => g (.inl (i,k)))+(fun g => g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_add_left (hm _) (hm _) (hm _)]
  simp [coordinate_covariance]

lemma goe_mulVec_memLp (r : ℝ) (m : ι → ℝ) (i : ι) :
    MemLp (fun g => (goeMatrix r g*ᵥm) i) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := memLp_finsetSum (Finset.univ : Finset ι)
    (fun k _ => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
  simpa only [mulVec,dotProduct] using hh

lemma goe_entry_observation_cov {r : ℝ} (hr : 0 ≤ r) (v : ℝ) (m : ι → ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
  have hW := (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two
  have hM := goe_mulVec_memLp r m l
  have hN := (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two.const_mul (sqrt v)
  change cov[fun g => goeMatrix r g i k,(fun g => (goeMatrix r g*ᵥm) l)+
    (fun g => sqrt v*g (.inr l));gaussianCoordinates (MatrixCoordinates ι)] = _
  rw [covariance_add_right hW hM hN,covariance_const_mul_right,goe_noise_cov,mul_zero,add_zero]
  change cov[fun g => goeMatrix r g i k,fun g => ∑ a, goeMatrix r g l a*m a;_]=_
  rw [covariance_fun_sum_right (fun a => (goe_matrix_gaussian (ι := ι) r).eval (l,a) |>.memLp_two.mul_const (m a)) hW]
  simp only [covariance_mul_const_right,goe_entry_cov hr]
  by_cases hil : i=l <;> by_cases hkl : k=l <;>
    simp [hil,hkl,mul_add,add_mul,Finset.sum_add_distrib]

lemma goe_mulVec_noise_cov (r : ℝ) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  change cov[fun g => ∑ a, goeMatrix r g i a*m a,fun g => g (.inr l);_]=_
  rw [covariance_fun_sum_left
    (fun a => (goe_matrix_gaussian (ι := ι) r).eval (i,a) |>.memLp_two.mul_const (m a))
    (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two]
  simp [covariance_mul_const_left,goe_noise_cov]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_mulVec_cov {r : ℝ} (hr : 0 ≤ r) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then ∑ k, m k^2 else 0)+m i*m l) := by
  have hc (k : ι) : cov[fun g => goeMatrix r g i k,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
    simpa only [goeObservation,sqrt_zero,zero_mul,add_zero] using
      goe_entry_observation_cov hr 0 m i k l
  change cov[fun g => ∑ k, goeMatrix r g i k*m k,fun g => (goeMatrix r g*ᵥm) l;_]=_
  rw [covariance_fun_sum_left
    (fun k => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
    (goe_mulVec_memLp r m l)]
  simp only [covariance_mul_const_left,hc]
  by_cases h : i=l
  · subst l
    simp [mul_add,add_mul,mul_assoc,← pow_two,Finset.sum_add_distrib,← Finset.mul_sum]
  · simp [h,mul_ite,ite_mul]
    ring

lemma goe_observation_mean (r v : ℝ) (m : ι → ℝ) (i : ι) :
    (∫ g, goeObservation r v m g i ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← observationCoeff_sample,mulVec,dotProduct] using
    linear_gaussian_mean (observationCoeff r v m i)

lemma goe_observation_cov {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) (i l : ι) :
    cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      (r*(∑ k,m k^2)+v)*(if i=l then 1 else 0)+r*m i*m l := by
  have hm (k : ι) := goe_mulVec_memLp r m k
  have hn (k : ι) := (coordinate_hasLaw (Sum.inr k : MatrixCoordinates ι)).hasGaussianLaw.memLp_two
  change cov[(fun g => (goeMatrix r g*ᵥm) i)+(fun g => sqrt v*g (.inr i)),
    (fun g => (goeMatrix r g*ᵥm) l)+(fun g => sqrt v*g (.inr l));_]=_
  rw [covariance_add_left (hm i) ((hn i).const_mul _) ((hm l).add ((hn l).const_mul _)),
    covariance_add_right (hm i) (hm l) ((hn l).const_mul _),
    covariance_add_right ((hn i).const_mul _) (hm l) ((hn l).const_mul _)]
  have hback : cov[fun g => g (.inr i),fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)]=0 := by
    rw [covariance_comm,goe_mulVec_noise_cov]
  rw [covariance_const_mul_right,goe_mulVec_noise_cov,mul_zero,add_zero,
    covariance_const_mul_left,hback,mul_zero,
    covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance,
    goe_mulVec_cov hr]
  simp only [Sum.inr.injEq]
  by_cases hil : i=l
  · simp only [hil,ite_true,mul_one]
    rw [mul_self_sqrt hv]
    ring
  · simp only [hil,ite_false,mul_zero,zero_add,add_zero]
    ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOERegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_observation_cov_matrix {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) :
    (fun i l => cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)])=rankOneCovariance (r*(m⬝ᵥm)+v) r m := by
  ext i l
  rw [goe_observation_cov hr hv]
  simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.vecMulVec_apply,dotProduct,← pow_two]
  ring

lemma goe_regression_covariance {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ)
    (p : ι × ι) (l : ι) :
    cov[fun g => goeMatrix r g p.1 p.2,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    ∑ k, goeRegressionCoefficient r v m p k *
      cov[fun g => goeObservation r v m g k,fun g => goeObservation r v m g l;
        gaussianCoordinates (MatrixCoordinates ι)] := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun k _ => mul_self_nonneg (m k))
  have hs : 0 < r*(m⬝ᵥm)+v := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  have hS : 0 < r*(m⬝ᵥm)+v+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  have hmat := goe_observation_cov_matrix hr hv.le m
  rw [goe_entry_observation_cov hr]
  change goeCrossCovariance r m p l =
    (goeRegressionCoefficient r v m * (show Matrix ι ι ℝ from fun k l => cov[fun g => goeObservation r v m g k,
      fun g => goeObservation r v m g l;gaussianCoordinates (MatrixCoordinates ι)])) p l
  rw [hmat,goeRegressionCoefficient,Matrix.mul_assoc,
    rankOneCovarianceInverse_mul _ _ _ hs.ne' hS.ne',Matrix.mul_one]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma radialDensity_pos {a : ℝ} (ha : 0 < a) (x : ι → ℝ) : 0 < radialDensity a x := by
  unfold radialDensity
  positivity

omit [DecidableEq ι] in
lemma radialDensity_le {a : ℝ} (ha : 0 < a) (x : ι → ℝ) :
    radialDensity a x ≤ ((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι) := by
  unfold radialDensity
  apply mul_le_of_le_one_right (by positivity)
  apply exp_le_one_iff.mpr
  have hx : 0 ≤ x⬝ᵥx := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (by positivity)

omit [DecidableEq ι] in
lemma continuous_rankOneDensity (s r : ℝ) (m : ι → ℝ) :
    Continuous (rankOneDensity s r m) := by
  unfold rankOneDensity radialDensity dotProduct
  fun_prop

omit [DecidableEq ι] in
lemma rankOneDensity_pos {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (m x : ι → ℝ) :
    0 < rankOneDensity s r m x := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  have hS : 0 < s+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  unfold rankOneDensity
  exact mul_pos (mul_pos (sqrt_pos.mpr (div_pos hs hS)) (radialDensity_pos (sqrt_pos.mpr hs) x)) (exp_pos _)

theorem goe_observation_density [Nonempty ι] {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v m)=
      (volume : Measure (ι → ℝ)).withDensity (fun x =>
        ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m x)) := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  apply gaussian_rankOne_covariance_density (goe_observation_joint_gaussian r v m).snd
    (add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv) hr m (goe_observation_mean r v m)
  intro i k
  exact congrFun (congrFun (goe_observation_cov_matrix hr hv.le m) i) k

lemma goe_noise_density [Nonempty ι] {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v 0)=
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (radialDensity (sqrt v) x)) := by
  rw [goe_observation_density hr hv]
  congr 1
  ext x
  simp [rankOneDensity,hv.ne']

lemma goe_noise_independent (r v : ℝ) :
    IndepFun (fun g (p : ι × ι) => goeMatrix r g p.1 p.2) (goeObservation r v 0)
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply (goe_observation_joint_gaussian r v 0).indepFun_of_covariance_eval
  intro p i
  have he (g : MatrixCoordinates ι → ℝ) : goeObservation r v 0 g i=sqrt v*g (.inr i) := by
    simp [goeObservation]
  simp only [he,covariance_const_mul_right,goe_noise_cov,mul_zero]

lemma goe_joint_noise_law (r v : ℝ) (m : ι → ℝ) :
    (((gaussianCoordinates (MatrixCoordinates ι)).map (fun g (p : ι × ι) => goeMatrix r g p.1 p.2)).prod
      ((gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v 0))).map
      (fun z : ((ι × ι) → ℝ) × (ι → ℝ) => (z.1,(fun i => ∑ k, z.1 (i,k)*m k)+z.2)) =
      (gaussianCoordinates (MatrixCoordinates ι)).map (fun g =>
        ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g)) := by
  have hXY := goe_observation_joint_gaussian (ι := ι) r v 0
  rw [← (goe_noise_independent (ι := ι) r v).map_prod_eq_prod_map_map hXY.fst.aemeasurable hXY.snd.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXY.aemeasurable]
  apply congrArg (fun f => (gaussianCoordinates (MatrixCoordinates ι)).map f)
  funext g
  apply Prod.ext
  · rfl
  ext i
  simp [goeObservation,mulVec,dotProduct]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ScalarGaussianReductionAlgebra
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma radialDensity_translate (a c : ℝ) (x m : ι → ℝ) :
    radialDensity a (x+c • m)=radialDensity a x*
      exp (-(2*c*(x⬝ᵥm)+c^2*(m⬝ᵥm))/(2*a^2)) := by
  unfold radialDensity
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm m x]
  have he : -(x⬝ᵥx+c*(x⬝ᵥm)+c*(x⬝ᵥm+c*(m⬝ᵥm)))/(2*a^2)=
      -(x⬝ᵥx)/(2*a^2)+(-(2*c*(x⬝ᵥm)+c^2*(m⬝ᵥm))/(2*a^2)) := by ring
  rw [he,exp_add]
  ring

lemma gaussian_density_shift (d : ℝ) {s : ℝ} (hs : 0 ≤ s) (y : ι → ℝ) :
    (∏ i,gaussianPDFReal d (NNReal.mk s hs) (y i))=
      radialDensity (sqrt s) (fun i => y i-d) := by
  have he (i : ι) : gaussianPDFReal d (NNReal.mk s hs) (y i)=
      gaussianPDFReal 0 (NNReal.mk s hs) (y i-d) := by simp [gaussianPDFReal]
  simp only [he]
  have hv : NNReal.mk s hs=NNReal.mk ((sqrt s)^2) (sq_nonneg (sqrt s)) := by
    ext
    exact (sq_sqrt hs).symm
  rw [hv,product_gaussianPDF_radial (sqrt_nonneg _)]

lemma scalar_gaussian_exponent {n s S j q b a : ℝ} (hn : n ≠ 0) (hs : s ≠ 0)
    (hS : S ≠ 0) (hSq : S=s+j*q) :
    -(2*(j*b)*(n*a)+(j*b)^2*(n*q))/(2*s)+
      (j/n)/(2*s*S)*(n*a+j*b*(n*q))^2+n*j*b^2/2 =
      n*j*(a-s*b)^2/(2*s*S) := by
  subst S
  field_simp
  ring

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

theorem rankOneDensity_cancellation {n s S j q b a : ℝ} (hn : n ≠ 0)
    (hs : 0 < s) (hS : S ≠ 0) (hSq : S=s+j*q)
    (x m : ι → ℝ) (hm : m⬝ᵥm=n*q) (hx : x⬝ᵥm=n*a) :
    rankOneDensity s (j/n) m (x+(j*b) • m)*exp (n*j*b^2/2) =
    sqrt (s/S)*radialDensity (sqrt s) x*exp (n*j*(a-s*b)^2/(2*s*S)) := by
  have he : s+(j/n)*(m⬝ᵥm)=S := by rw [hm,hSq]; field_simp
  rw [rankOneDensity,he,radialDensity_translate,sq_sqrt hs.le,hm,hx]
  simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm m x,hm,hx]
  have hE := scalar_gaussian_exponent hn hs.ne' hS hSq (j := j) (q := q) (b := b) (a := a)
  calc
    _ = sqrt (s/S)*radialDensity (sqrt s) x*
        exp (-(2*(j*b)*(n*a)+(j*b)^2*(n*q))/(2*s)+
          (j/n)/(2*s*S)*(n*a+j*b*(n*q))^2+n*j*b^2/2) := by rw [exp_add,exp_add]; ring
    _ = _ := by rw [hE]

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma pi_gaussian_convolution (m₁ m₂ : ι → ℝ) (v₁ v₂ : ι → ℝ≥0) :
    ((Measure.pi (fun i=>gaussianReal (m₁ i) (v₁ i))).prod
      (Measure.pi (fun i=>gaussianReal (m₂ i) (v₂ i)))).map (fun p=>p.1+p.2)=
    Measure.pi (fun i=>gaussianReal (m₁ i+m₂ i) (v₁ i+v₂ i)) := by
  have h := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun i=>gaussianReal (m₁ i) (v₁ i)) (fun i=>gaussianReal (m₂ i) (v₂ i))).map_eq
  rw [← h,Measure.map_map (by fun_prop) (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).measurable]
  change (Measure.pi (fun i=>(gaussianReal (m₁ i) (v₁ i)).prod (gaussianReal (m₂ i) (v₂ i)))).map
    (fun x i=> (x i).1+(x i).2)=_
  have (i : ι) : IsProbabilityMeasure (((gaussianReal (m₁ i) (v₁ i)).prod
      (gaussianReal (m₂ i) (v₂ i))).map (fun p : ℝ×ℝ=>p.1+p.2)) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  rw [Measure.pi_map_pi (f := fun (_ : ι) (p : ℝ×ℝ)=>p.1+p.2) (fun _=>by fun_prop)]
  congr 1
  funext i
  exact gaussianReal_conv_gaussianReal

theorem continuous_convolution_density (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {φ p : (ι → ℝ) → ℝ} (hφ : Continuous φ) (hp : Continuous p)
    (hφpos : ∀ x,0 ≤ φ x)
    {C : ℝ} (hφC : ∀ x,φ x ≤ C)
    (hconv : (μ.prod ((volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (φ x)))).map
      (fun q=>q.1+q.2)=(volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (p x)))
    (z : ι → ℝ) :
    (∫⁻ x, ENNReal.ofReal (φ (z-x)) ∂μ)=ENNReal.ofReal (p z) := by
  let K : (ι → ℝ) → ℝ≥0∞ := fun y=>∫⁻ x,ENNReal.ofReal (φ (y-x)) ∂μ
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hae : K=ᵐ[volume] (fun y=>ENNReal.ofReal (p y)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hK.aemeasurable hp.measurable.ennreal_ofReal.aemeasurable).mp
    ext s hs
    rw [withDensity_apply _ hs,withDensity_apply _ hs]
    let F : (ι → ℝ) × (ι → ℝ) → ℝ≥0∞ := fun q=>s.indicator (fun _=>1) q.2
    have hF : Measurable F := measurable_const.indicator (hs.preimage measurable_snd)
    have hh := additive_noise_lintegral μ (fun x=>ENNReal.ofReal (φ x))
      hφ.measurable.ennreal_ofReal id measurable_id F hF
    have hm : Measurable (s.indicator (fun _=> (1 : ℝ≥0∞))) := measurable_const.indicator hs
    have he := congrArg (fun ν=>∫⁻ y,s.indicator (fun _=> (1 : ℝ≥0∞)) y ∂ν) hconv
    rw [lintegral_map hm (by fun_prop),lintegral_withDensity_eq_lintegral_mul _
      hp.measurable.ennreal_ofReal hm] at he
    change (∫⁻ q,F (q.1,id q.1+q.2) ∂μ.prod (volume.withDensity (fun x=>ENNReal.ofReal (φ x))))=_ at he
    rw [hh] at he
    have hleft (y : ι → ℝ) : (∫⁻ x, ENNReal.ofReal (φ (y-id x))*F (x,y) ∂μ)=s.indicator K y := by
      by_cases hy : y∈s <;> simp [F,K,hy]
    have hright (y : ι → ℝ) : ENNReal.ofReal (p y)*s.indicator (fun _=>(1 : ℝ≥0∞)) y=
        s.indicator (fun y=>ENNReal.ofReal (p y)) y := by by_cases hy : y∈s <;> simp [hy]
    simp only [Pi.mul_apply,hleft,hright,lintegral_indicator hs] at he
    exact he
  have hi (y : ι → ℝ) : Integrable (fun x=>φ (y-x)) μ :=
    integrable_bounded μ (by fun_prop) (fun x=>by rw [norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
  have hc : Continuous (fun y : ι → ℝ=>∫ x,φ (y-x) ∂μ) := by
    apply continuous_of_dominated (bound := fun _=>C)
    · intro y; exact (hi y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun x=>by rw [norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
    · exact integrable_const C
    · exact Filter.Eventually.of_forall (fun x=>by fun_prop)
  have he (y : ι → ℝ) : K y=ENNReal.ofReal (∫ x,φ (y-x) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi y) (Filter.Eventually.of_forall (fun x=>hφpos _))).symm
  have hcont : Continuous K := by rw [show K=(fun y=>ENNReal.ofReal (∫ x,φ (y-x) ∂μ)) from funext he]; exact ENNReal.continuous_ofReal.comp hc
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (ι → ℝ)) hcont
    (ENNReal.continuous_ofReal.comp hp)).mp hae) z

theorem gaussian_radial_convolution {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ) (z : ι → ℝ) :
    (∫⁻ x, ENNReal.ofReal (radialDensity σ (z-x))
      ∂Measure.pi (fun _ : ι=>gaussianReal 0 t.toNNReal))=
    ENNReal.ofReal (radialDensity (sqrt (t+σ^2)) z) := by
  classical
  have hv : 0 < t+σ^2 := add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)
  have hnoise : Measure.pi (fun _ : ι=>gaussianReal 0 (NNReal.mk (σ^2) (sq_nonneg σ)))=
      (volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (radialDensity σ x)) := by
    rw [pi_gaussian_density _ _ (fun _=>by intro hh; have hh' := congrArg (fun r : ℝ≥0=>(r:ℝ)) hh; exact (sq_pos_of_pos hσ).ne' hh')]
    congr 1; funext x; rw [product_gaussianPDF_radial hσ.le]
  have hout : Measure.pi (fun _ : ι=>gaussianReal 0 (t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)))=
      (volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (radialDensity (sqrt (t+σ^2)) x)) := by
    rw [pi_gaussian_density _ _ (fun _=>by
      have he : (↑(t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)):ℝ)=t+σ^2 := by simp [Real.coe_toNNReal _ ht]
      exact_mod_cast (show (↑(t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)):ℝ)≠0 by rw [he]; exact hv.ne'))]
    congr 1; funext x
    have he : t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)=NNReal.mk ((sqrt (t+σ^2))^2) (sq_nonneg _) := by
      ext; simp [Real.coe_toNNReal _ ht,sq_sqrt hv.le]
    rw [he,product_gaussianPDF_radial (sqrt_nonneg _)]
  apply continuous_convolution_density _ (continuous_radialDensity σ)
    (continuous_radialDensity _) (fun x=>(radialDensity_pos hσ x).le)
    (radialDensity_le hσ)
  rw [← hnoise,pi_gaussian_convolution]
  simpa only [zero_add] using hout
end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ConditionalBadSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma isClosed_badFieldSet (n : ℕ) (j A ε c : ℝ) : IsClosed (badFieldSet n j A ε c) := by
  let X := ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  let : CompactSpace ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ))) :=
    {p | (∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2) ≤ ε^2*(n:ℝ) ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1) (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp ≤ c}
  have ha (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.1:Fin n → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hx (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin n=>ℝ)).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hy (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      tanh (p.2.2 i)) := continuous_tanh.comp ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        ∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2)
        (g := fun _ => ε^2*(n:ℝ)) (by
        apply continuous_finsetSum
        intro i _
        exact ((ha i).sub (continuous_const.sub ((hy i).pow 2))).pow 2) continuous_const
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1)
          (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp) (g := fun _=>c) (by
        dsimp [X,quadraticForm,fieldHessian,hessianCore,plantedInteraction,onsager,overlap,magnetization]
        apply continuous_finsetSum; intro i _
        apply continuous_finsetSum; intro k _
        apply Continuous.mul _ (hx k)
        apply Continuous.mul (hx i)
        apply Continuous.add continuous_const
        apply Continuous.mul _ (Real.continuous_sqrt.comp (ha k))
        apply Continuous.mul (Real.continuous_sqrt.comp (ha i))
        exact (((continuous_const.mul (continuous_const.sub
          ((continuous_finsetSum _ (fun l _ => (hy l).pow 2)).div_const _))).mul continuous_const).sub
          ((by fun_prop : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) => p.2.1 i k)).add continuous_const)).sub
          (((continuous_const.mul (hy i))).mul (hy k))) continuous_const
  have hproj := isClosedMap_snd_of_compactSpace S hS
  convert hproj using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨a,ha,hclose,x,hx,hquad⟩
    have ha' : a ∈ Icc (0 : Fin n → ℝ) (fun _=>A) := ⟨fun i=>(ha i).1,fun i=>(ha i).2⟩
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    exact ⟨((⟨a,ha'⟩,⟨x,hx'⟩),p),⟨hclose,hquad⟩,rfl⟩
  · rintro ⟨⟨⟨a,x⟩,p'⟩,hS,rfl⟩
    exact ⟨a,fun i=>⟨a.2.1 i,a.2.2 i⟩,hS.1,x,by simpa only [Metric.mem_sphere,dist_zero_right] using x.2,hS.2⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianQuadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKGap
open scoped BigOperators

lemma gaussian_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x^k) (gaussianReal 0 1) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq, norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 1) (k : ℝ≥0∞) (by simp)).integrable_norm_pow'

lemma gaussian_memLp_sq : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_integrable_pow 4

lemma gaussian_integral_sq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero, NNReal.coe_one] using h

lemma gaussian_integral_fourth : (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x^3) (3*x^2) x := by
    convert! (hasDerivAt_id x).pow 3 using 1; norm_num [Pi.pow_apply, id_eq]
  have hi : Integrable (fun x : ℝ => (x - 0)*x^3) (gaussianReal 0 1) := by
    simpa only [sub_zero, ← pow_succ'] using gaussian_integrable_pow 4
  have h := gaussian_integration_by_parts (by norm_num : (1 : ℝ≥0) ≠ 0)
    hd (gaussian_integrable_pow 3) ((gaussian_integrable_pow 2).const_mul 3) hi
  simpa only [sub_zero, ← pow_succ', integral_const_mul, gaussian_integral_sq,
    NNReal.coe_one, one_mul, mul_one] using h

section Quadratic
variable {ι : Type*} [Fintype ι]

lemma gaussianQuadratic_memLp (a : ι → ℝ) :
    MemLp (gaussianQuadratic a) 2 (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply memLp_finsetSum
  intro i _
  exact ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i))

lemma gaussianQuadratic_mean (a : ι → ℝ) :
    (∫ x, gaussianQuadratic a x ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = ∑ i, a i := by
  unfold gaussianQuadratic
  have hi (i : ι) : Integrable (fun x : ι → ℝ => a i * (x i)^2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    ((gaussian_memLp_sq.const_mul (a i)).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)).integrable (by norm_num)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  have he : (∫ x : ι → ℝ, (x i)^2 ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ y : ℝ, y^2 ∂gaussianReal 0 1 :=
    integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      (f := fun y : ℝ => y^2) (by fun_prop)
  rw [he, gaussian_integral_sq, mul_one]

end Quadratic

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixWhitening
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype κ] in
lemma positive_sqrt_data {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R*R=S ∧ IsUnit R.det := by
  let R := CFC.sqrt S
  have hR : R.IsHermitian := (CFC.sqrt_nonneg S).posSemidef.isHermitian
  have hsq : R*R=S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hu : IsUnit R := isUnit_of_mul_isUnit_left (hsq.symm ▸ hS.isUnit)
  exact ⟨R,hR,hsq,(Matrix.isUnit_iff_isUnit_det R).mp hu⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_WeightedMomentComparison
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma sum_abs_le_sqrt_card_l2 (d : ι → ℝ) :
    (∑ i, |d i|) ≤ √(Fintype.card ι:ℝ)*√(∑ i,d i^2) := by
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι => (1:ℝ)) (fun i => |d i|)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_ConditionalObservationData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarA_empirical_sum {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    ∑ i,tanh (y i)*(y i-scalarD j (empiricalLaw y,t,σ))=
      (n:ℝ)*scalarA j (empiricalLaw y,t,σ) := by
  simp only [scalarA,scalarM,integral_empiricalLaw,Fintype.card_fin]
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [mul_sub,← mul_assoc,mul_inv_cancel₀ hn,one_mul]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _; ring
  · rw [← Finset.sum_mul]
    field_simp

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEPointwisePosterior
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity GaussianRegression
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem goe_pointwise_posterior {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m z : ι → ℝ) :
    (goeLaw (ι := ι) r).withDensity (fun W => ENNReal.ofReal
      (radialDensity (sqrt v) (z-(fun i => ∑ k, W (i,k)*m k)))) =
    ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m z) • conditionalGoeLaw r v m z := by
  have hXY := goe_observation_joint_gaussian r v m
  let : IsProbabilityMeasure (goeLaw (ι := ι) r) :=
    Measure.isProbabilityMeasure_map (measurable_pi_lambda _ fun p => by unfold goeMatrix; fun_prop).aemeasurable
  let ρ := (gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v m)
  have hreg := regression_joint_law hXY (goeRegressionCoefficient r v m) (goe_regression_covariance hr hv m)
  have hj := goe_joint_noise_law r v m
  rw [goe_noise_density hr hv] at hj
  rw [goe_observation_density hr hv m] at hreg
  have hjoint : ((goeLaw (ι := ι) r).prod ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (radialDensity (sqrt v) x)))).map
      (fun q => (q.1,(fun i => ∑ k, q.1 (i,k)*m k)+q.2)) =
    (ρ.prod ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m x)))).map
      (fun q => (q.1+goeRegressionCoefficient r v m*ᵥq.2,q.2)) := hj.trans hreg
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  have hs := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  exact continuous_kernel_posterior (goeLaw (ι := ι) r) ρ (continuous_radialDensity _)
    (continuous_rankOneDensity _ _ m) (fun x => (radialDensity_pos (sqrt_pos.mpr hv) x).le)
    (fun x => (rankOneDensity_pos hs hr m x).le) (by positivity)
    (radialDensity_le (sqrt_pos.mpr hv)) (by fun_prop) (by fun_prop) hjoint z

theorem goe_pointwise_conditional_integral {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    (m z : ι → ℝ) (f : ((ι × ι) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, ENNReal.ofReal (radialDensity (sqrt v) (z-goeMatrix r g*ᵥm))*
      f (fun p => goeMatrix r g p.1 p.2) ∂gaussianCoordinates (MatrixCoordinates ι)) =
    ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m z)*
      (∫⁻ W, f W ∂conditionalGoeLaw r v m z) := by
  have hh := congrArg (fun ν => ∫⁻ W, f W ∂ν) (goe_pointwise_posterior hr hv m z)
  have hφ : Measurable (fun W : (ι × ι) → ℝ => ENNReal.ofReal (radialDensity (sqrt v) (z-(fun i => ∑ k, W (i,k)*m k)))) :=
    ((continuous_radialDensity _).comp (by fun_prop)).measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hf,lintegral_smul_measure] at hh
  rw [goeLaw,lintegral_map (hφ.mul hf) (by unfold goeMatrix; fun_prop)] at hh
  exact hh

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalHessianLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarQMoment_empirical_overlap {n : ℕ} [NeZero n] (y : Fin n → ℝ) :
    scalarQMoment (empiricalLaw y)=overlap y := by
  simp only [scalarQMoment,integral_empiricalLaw,Fintype.card_fin,overlap,magnetization,
    div_eq_mul_inv,mul_comm]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianReductionPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma tapField_planted_observation {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y x : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    tapField j (plantedInteraction j W) (fun i=>t+x i) y=
      empiricalObservation j t σ y-W*ᵥmagnetization y-x := by
  ext i
  simp only [tapField,plantedInteraction,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,vecMulVec_apply,mul_one,add_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,empiricalObservation,scalarD,scalarM,integral_empiricalLaw,
    Fintype.card_fin,scalarBMoment,scalarQMoment_empirical_overlap,onsager,
    magnetization,Pi.sub_apply,Matrix.mulVec,dotProduct]
  ring

lemma scalar_density_cancellation {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) :
    rankOneDensity ((j/(n:ℝ))*(magnetization y⬝ᵥmagnetization y)+(t+σ^2))
      (j/(n:ℝ)) (magnetization y) (empiricalObservation j t σ y)*
      exp ((n:ℝ)*j*(1-overlap y)^2/2)=
    sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y := by
  let p := scalarEmpirical y t σ
  let q := scalarQMoment (empiricalLaw y)
  let s := scalarS j p
  let S := s+j*q
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hq : 0 ≤ q := (scalarQMoment_bounds _).1
  have hs : 0 < s := add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) (mul_nonneg hj hq)
  have hS : 0 < S := add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq)
  have hm : magnetization y⬝ᵥmagnetization y=(n:ℝ)*q := by
    dsimp [q]
    rw [scalarQMoment_empirical_overlap]
    simp only [overlap,magnetization,dotProduct,← pow_two]
    field_simp
  have hx : (fun i=>y i-scalarD j p)⬝ᵥmagnetization y=(n:ℝ)*scalarA j p := by
    rw [dotProduct_comm]
    exact scalarA_empirical_sum j t σ y
  have hs' : (j/(n:ℝ))*(magnetization y⬝ᵥmagnetization y)+(t+σ^2)=s := by
    rw [hm]; dsimp [s,scalarS,p,scalarEmpirical,q]; field_simp; ring
  rw [hs']
  have hobs : empiricalObservation j t σ y=(fun i=>y i-scalarD j p)+(j*(1-q)) • magnetization y := rfl
  rw [hobs]
  have hc := rankOneDensity_cancellation hn hs hS.ne' (rfl : S=s+j*q)
    (fun i=>y i-scalarD j p) (magnetization y) hm hx (b := 1-q)
  have hb : 1-overlap y=1-q := by rw [← scalarQMoment_empirical_overlap]
  rw [hb,hc]
  have hd : productNormal (scalarD j p) s y=radialDensity (sqrt s) (fun i=>y i-scalarD j p) := by
    unfold productNormal
    rw [show s.toNNReal=NNReal.mk s hs.le from by ext; exact Real.coe_toNNReal _ hs.le]
    exact gaussian_density_shift _ hs.le y
  rw [scalarIntegrand,show scalarEmpirical y t σ=p from rfl,hd]
  simp only [Fintype.card_fin]
  have he : (n:ℝ)*j*(scalarA j p-s*(1-q))^2/(2*s*S)=(n:ℝ)*scalarPsi j p := by
    dsimp [S,s,q,p,scalarPsi,scalarEmpirical]
    ring
  rw [he]
  ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianVectorMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal

lemma gaussian_integral_fourth_variance (v : ℝ≥0) :
    (∫ x : ℝ,x^4 ∂gaussianReal 0 v)=3*(v:ℝ)^2 := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => sqrt (v:ℝ)*x)=gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hm,integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow,integral_const_mul,gaussian_integral_fourth]
  rw [show sqrt (v:ℝ)^4=(v:ℝ)^2 by rw [show 4=2*2 by norm_num,pow_mul,Real.sq_sqrt v.coe_nonneg]]
  ring

lemma gaussian_fourth_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [id_eq,norm_pow] using
    (IsGaussian.memLp_id (gaussianReal 0 v) (4:ℝ≥0∞) (by norm_num)).integrable_norm_pow'

lemma linear_gaussian_fourth {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℝ) :
    (∫ g,(∑ i,a i*g i)^4 ∂gaussianCoordinates κ)=3*(∑ i,a i^2)^2 := by
  let A : Matrix Unit κ ℝ := fun _ => a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ → ℝ => ∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  have hm := linear_gaussian_mean a
  have hv : Var[fun g => ∑ i,a i*g i;gaussianCoordinates κ]=∑ i,a i^2 := by
    rw [← covariance_self hg.aemeasurable]
    simpa only [sq] using linear_gaussian_covariance a a
  change HasLaw (fun g : κ → ℝ => ∑ i,a i*g i) _ _ at hl
  rw [hm,hv] at hl
  have he := hl.integral_comp (f := fun x : ℝ => x^4) (by fun_prop)
  simp only [Function.comp_def] at he
  rw [he,gaussian_integral_fourth_variance]
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)))]

lemma linear_gaussian_fourth_integrable {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    Integrable (fun g => (∑ i,a i*g i)^4) (gaussianCoordinates κ) := by
  let A : Matrix Unit κ ℝ := fun _ => a
  have hg := (matrix_sample_gaussian A).eval ()
  change HasGaussianLaw (fun g : κ → ℝ => ∑ i,a i*g i) (gaussianCoordinates κ) at hg
  have hl : HasLaw _ _ _ := ⟨hg.aemeasurable,hg.map_eq_gaussianReal⟩
  rw [linear_gaussian_mean a] at hl
  have hi := gaussian_fourth_integrable (Var[fun g : κ → ℝ => ∑ i,a i*g i;gaussianCoordinates κ].toNNReal)
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop) hl.aemeasurable).mp hi

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPScalarTaylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set

lemma scalar_remainder_of_lipschitz_derivative {f f' : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hl : ∀ x y, |f' x-f' y| ≤ L*|x-y|) (x d : ℝ) :
    |f (x+d)-f x-f' x*d| ≤ L*d^2 := by
  let R : ℝ → ℝ := fun z => f z-f x-f' x*(z-x)
  have hder (z : ℝ) : HasDerivAt R (f' z-f' x) z := by
    dsimp [R]
    convert! ((hd z).sub_const (f x)).sub (((hasDerivAt_id z).sub_const x).const_mul (f' x)) using 1; simp
  have bnd (z : ℝ) (hz : z ∈ segment ℝ x (x+d)) : ‖f' z-f' x‖ ≤ L*|d| := by
    rw [Real.norm_eq_abs]
    apply (hl z x).trans
    apply mul_le_mul_of_nonneg_left _ hL
    simpa only [Real.norm_eq_abs,add_sub_cancel_left] using norm_sub_le_of_mem_segment hz
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ x (x+d)) => (hder z).hasDerivWithinAt) bnd
    (convex_segment x (x+d)) (left_mem_segment ℝ x (x+d)) (right_mem_segment ℝ x (x+d))
  simpa only [R,sub_self,mul_zero,sub_zero,add_sub_cancel_left,Real.norm_eq_abs,
    mul_assoc,← pow_two,sq_abs] using hh

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma scalar_variance_lipschitz_abs (x y : ℝ) :
    |(1-tanh x^2)-(1-tanh y^2)| ≤ 2*|x-y| := by
  have hsum : |tanh x+tanh y| ≤ 2 := (abs_add_le _ _).trans (by
    linarith [(abs_tanh_lt_one x).le,(abs_tanh_lt_one y).le])
  calc
    _ = |tanh x-tanh y| * |tanh x+tanh y| := by
      rw [show (1-tanh x^2)-(1-tanh y^2) = -((tanh x-tanh y)*(tanh x+tanh y)) by ring, abs_neg, abs_mul]
    _ ≤ |x-y| * 2 := mul_le_mul (tanh_lipschitz_abs x y) hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := mul_comm _ _

lemma tanh_scalar_remainder (x d : ℝ) :
    |tanh (x+d)-tanh x-(1-tanh x^2)*d| ≤ 2*d^2 :=
  scalar_remainder_of_lipschitz_derivative (by norm_num) hasDerivAt_tanh
    scalar_variance_lipschitz_abs x d

lemma scalar_variance_hasDeriv (x : ℝ) :
    HasDerivAt (fun z => 1-tanh z^2) (-2*tanh x*(1-tanh x^2)) x := by
  convert! (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_tanh x).pow 2) using 1; ring

lemma scalar_variance_deriv_lipschitz_abs (x y : ℝ) :
    |(-2*tanh x*(1-tanh x^2))-(-2*tanh y*(1-tanh y^2))| ≤ 6*|x-y| := by
  have hu : |tanh x| ≤ 1 := (abs_tanh_lt_one x).le
  have hv : |1-tanh y^2| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one y).le)]
    linarith [sq_nonneg (tanh y)]
  calc
    _ = 2*|tanh x*((1-tanh x^2)-(1-tanh y^2))+
        (tanh x-tanh y)*(1-tanh y^2)| := by
      rw [show (-2*tanh x*(1-tanh x^2))-(-2*tanh y*(1-tanh y^2))=
        -(2*(tanh x*((1-tanh x^2)-(1-tanh y^2))+
        (tanh x-tanh y)*(1-tanh y^2))) by ring,abs_neg,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ 2*(|tanh x| * |(1-tanh x^2)-(1-tanh y^2)|+
        |tanh x-tanh y| * |1-tanh y^2|) := by gcongr; exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
    _ ≤ 2*(1*(2*|x-y|)+|x-y| * 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (mul_le_mul hu (scalar_variance_lipschitz_abs x y) (abs_nonneg _) (by norm_num))
        (mul_le_mul (tanh_lipschitz_abs x y) hv (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

lemma scalar_variance_remainder (x d : ℝ) :
    |(1-tanh (x+d)^2)-(1-tanh x^2)-(-2*tanh x*(1-tanh x^2))*d| ≤ 6*d^2 :=
  scalar_remainder_of_lipschitz_derivative (by norm_num) scalar_variance_hasDeriv
    scalar_variance_deriv_lipschitz_abs x d
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPVectorTaylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators

lemma varianceAverage_eq_average {n : ℕ} (hn : 0 < n) (y : Field n) :
    varianceAverage y=(∑ i,spinVariance y i)/(n:ℝ) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  dsimp [varianceAverage,overlap,spinVariance]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  field_simp

lemma varianceAverage_bounds {n : ℕ} (hn : 0 < n) (y : Field n) :
    0 ≤ varianceAverage y ∧ varianceAverage y ≤ 1 := by
  dsimp [varianceAverage]
  exact ⟨sub_nonneg.mpr (overlap_lt_one hn y).le,sub_le_self _ (overlap_nonneg y)⟩

lemma magnetization_norm_bound {n : ℕ} (y : Field n) :
    vectorNorm (magnetization y) ≤ sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (sqrt_nonneg _)).mp
  rw [vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : Fin n,(1:ℝ) := Finset.sum_le_sum (fun i _ => (tanh_sq_lt_one (y i)).le)
    _ = _ := by simp

lemma vectorNorm_le_of_sq_sum {n : ℕ} {v : Field n} {c : ℝ} (hc : 0 ≤ c)
    (hb : ∑ i,v i^2 ≤ c^2) : vectorNorm v ≤ c := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) hc).mp
  exact (vectorNorm_sq v).trans_le hb

lemma magnetization_difference_norm {n : ℕ} (y d : Field n) :
    vectorNorm (magnetization (y+d)-magnetization y) ≤ vectorNorm d := by
  apply vectorNorm_le_of_sq_sum (vectorNorm_nonneg _)
  rw [vectorNorm_sq]
  apply Finset.sum_le_sum
  intro i _
  have hh := tanh_lipschitz_abs (y i+d i) (y i)
  rw [add_sub_cancel_left] at hh
  simpa only [Pi.sub_apply,Pi.add_apply,magnetization,sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hh |>.trans_eq (sq_abs (d i))

lemma magnetization_remainder_norm {n : ℕ} (y d : Field n) :
    vectorNorm (magnetizationRemainder y d) ≤ 2*sqrt (∑ i,d i^4) := by
  apply vectorNorm_le_of_sq_sum (by positivity)
  rw [mul_pow,Real.sq_sqrt (Finset.sum_nonneg (fun i _ => (by positivity : 0 ≤ d i^4))),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := tanh_scalar_remainder (y i) (d i)
  have hh' := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hh
  simpa only [magnetizationRemainder,Pi.sub_apply,Pi.add_apply,magnetization,spinVariance,
    sq_abs,mul_pow,← pow_mul] using hh'

lemma varianceAverage_remainder {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)-varianceAverage y-varianceLinear y d| ≤
      6/(n:ℝ)*vectorNorm d^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [varianceAverage_eq_average hn,varianceAverage_eq_average hn,vectorNorm_sq]
  have he : (∑ i,spinVariance (y+d) i)/(n:ℝ)-
      (∑ i,spinVariance y i)/(n:ℝ)-varianceLinear y d=
      (∑ i,(spinVariance (y+d) i-spinVariance y i-
        (-2*magnetization y i*spinVariance y i)*d i))/(n:ℝ) := by
    have hlin : (∑ i,(-2*magnetization y i*spinVariance y i)*d i)=
        -2*∑ i,magnetization y i*spinVariance y i*d i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _; ring
    simp only [varianceLinear,Finset.sum_sub_distrib,hlin]
    field_simp
  rw [he,abs_div,abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ∑ i,|(spinVariance (y+d) i-spinVariance y i-(-2*magnetization y i*spinVariance y i)*d i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,6*d i^2 := Finset.sum_le_sum (fun i _ => scalar_variance_remainder (y i) (d i))
    _ = _ := by simp only [vectorSqNorm,← Finset.mul_sum]; field_simp

lemma varianceAverage_difference {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)-varianceAverage y| ≤ 2/sqrt (n:ℝ)*vectorNorm d := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn0)
  rw [varianceAverage_eq_average hn,varianceAverage_eq_average hn,← sub_div,
    ← Finset.sum_sub_distrib,abs_div,abs_of_pos hn0]
  apply (div_le_iff₀ hn0).mpr
  calc
    _ ≤ ∑ i,|spinVariance (y+d) i-spinVariance y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,2*|d i| := Finset.sum_le_sum (fun i _ => by
      simpa only [spinVariance,magnetization,Pi.add_apply,add_sub_cancel_left] using scalar_variance_lipschitz_abs (y i+d i) (y i))
    _ = 2*∑ i,|d i| := by rw [Finset.mul_sum]
    _ ≤ 2*(sqrt (n:ℝ)*vectorNorm d) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hh := sum_abs_le_sqrt_card_l2 d
      have he : sqrt (∑ i,d i^2)=vectorNorm d := by
        change sqrt (vectorSqNorm d)=vectorNorm d
        rw [← vectorNorm_sq,Real.sqrt_sq (vectorNorm_nonneg _)]
      simpa only [Fintype.card_fin,he] using hh
    _ = _ := by field_simp; rw [Real.sq_sqrt hn0.le]; ring

lemma tap_remainder_identity {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y d : Field n) :
    tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd=
      (j*varianceAverage y) • magnetizationRemainder y d+
      (j*(varianceAverage (y+d)-varianceAverage y-varianceLinear y d)) • magnetization y+
      (j*(varianceAverage (y+d)-varianceAverage y)) • (magnetization (y+d)-magnetization y)-
      J*ᵥmagnetizationRemainder y d := by
  have hjac (i : Fin n) : (fieldJacobian j J y*ᵥd) i=
      d i+onsager j y*(spinVariance y i*d i)-
      (∑ k,J i k*(spinVariance y k*d k))+j*varianceLinear y d*magnetization y i := by
    change (∑ k,fieldJacobian j J y i k*d k)=_
    have he : (∑ k,fieldJacobian j J y i k*d k)=
        (∑ k,(if i=k then 1 else (0:ℝ))*d k)+
        onsager j y*(∑ k,(if i=k then 1 else (0:ℝ))*spinVariance y k*d k)-
        (∑ k,J i k*(spinVariance y k*d k))-
        (2*j/(n:ℝ))*magnetization y i*(∑ k,magnetization y k*spinVariance y k*d k) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [fieldJacobian,hessianCore]
      ring
    rw [he]
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    dsimp [varianceLinear]
    ring
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [hjac]
  simp only [tapField,Pi.add_apply,onsager,varianceAverage,magnetizationRemainder,Pi.sub_apply,
    Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib]
  ring

attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

theorem tap_remainder_norm {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y d : Field n) :
    vectorNorm (tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd) ≤
      2*(j+K)*sqrt (∑ i,d i^4)+(8*j/sqrt (n:ℝ))*vectorNorm d^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hsn : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr hn0)
  have hnd := vectorNorm_nonneg d
  let rm := magnetizationRemainder y d
  let rb := varianceAverage (y+d)-varianceAverage y-varianceLinear y d
  let db := varianceAverage (y+d)-varianceAverage y
  have hb := varianceAverage_bounds hn y
  have h₁ : vectorNorm ((j*varianceAverage y) • rm) ≤ j*vectorNorm rm := by
    change vectorNorm (fun i => (j*varianceAverage y)*rm i) ≤ _
    rw [vectorNorm_smul,abs_of_nonneg (mul_nonneg hj hb.1)]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hb.2]) (vectorNorm_nonneg _)
  have h₂ : vectorNorm ((j*rb) • magnetization y) ≤
      (6*j/sqrt (n:ℝ))*vectorNorm d^2 := by
    change vectorNorm (fun i => (j*rb)*magnetization y i) ≤ _
    rw [vectorNorm_smul,abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ (j*(6/(n:ℝ)*vectorNorm d^2))*sqrt (n:ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (varianceAverage_remainder hn y d) hj)
          (magnetization_norm_bound y) (vectorNorm_nonneg _) (by positivity)
      _ = _ := by field_simp; rw [Real.sq_sqrt hn0.le]; ring
  have h₃ : vectorNorm ((j*db) • (magnetization (y+d)-magnetization y)) ≤
      (2*j/sqrt (n:ℝ))*vectorNorm d^2 := by
    change vectorNorm (fun i => (j*db)*(magnetization (y+d)-magnetization y) i) ≤ _
    rw [vectorNorm_smul,abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ (j*(2/sqrt (n:ℝ)*vectorNorm d))*vectorNorm d :=
        mul_le_mul (mul_le_mul_of_nonneg_left (varianceAverage_difference hn y d) hj)
          (magnetization_difference_norm y d) (vectorNorm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [tap_remainder_identity]
  calc
    _ ≤ (vectorNorm ((j*varianceAverage y) • rm)+vectorNorm ((j*rb) • magnetization y)+
      vectorNorm ((j*db) • (magnetization (y+d)-magnetization y)))+vectorNorm (J*ᵥrm) := by
        exact (vectorNorm_sub_le _ _).trans
          (add_le_add ((vectorNorm_add_le _ _).trans
            (add_le_add (vectorNorm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (j*vectorNorm rm+(6*j/sqrt (n:ℝ))*vectorNorm d^2+
      (2*j/sqrt (n:ℝ))*vectorNorm d^2)+K*vectorNorm rm :=
        add_le_add (add_le_add (add_le_add h₁ h₂) h₃) (hJ rm)
    _ = (j+K)*vectorNorm rm+(8*j/sqrt (n:ℝ))*vectorNorm d^2 := by ring
    _ ≤ (j+K)*(2*sqrt (∑ i,d i^4))+(8*j/sqrt (n:ℝ))*vectorNorm d^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (magnetization_remainder_norm y d) (add_nonneg hj hK)) le_rfl
    _ = _ := by ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalWhitening
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators MatrixOrder

lemma vectorNorm_sq_dot {n : ℕ} (x : Field n) : vectorNorm x^2=x⬝ᵥx := by
  rw [vectorNorm_sq]
  simp only [vectorSqNorm,dotProduct,pow_two]

lemma gram_energy {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (x : Field n) :
    x⬝ᵥ((Lᵀ*L)*ᵥx)=vectorNorm (L*ᵥx)^2 := by
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec,vectorNorm_sq_dot]

lemma regularizedGram_posDef {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {γ : ℝ} (hγ : 0 < γ) : (Lᵀ*L+γ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have hL : (Lᵀ*L).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self L
  exact Matrix.PosDef.posSemidef_add hL (Matrix.PosDef.one.smul hγ)

lemma squareRoot_energy {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsHermitian) (γ : ℝ) (hRR : R*R=Lᵀ*L+γ • 1) (x : Field n) :
    vectorNorm (R*ᵥx)^2=vectorNorm (L*ᵥx)^2+γ*vectorNorm x^2 := by
  have ht : Rᵀ=R := hR.eq
  rw [← gram_energy,ht,hRR,Matrix.add_mulVec,dotProduct_add,gram_energy,
    Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]
  simp only [vectorNorm_sq_dot]

theorem localGaussian_whitening {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U.IsHermitian ∧ IsUnit U.det ∧
      U*(Lᵀ*L+γ • 1)*U=1 ∧
      (∀ g : Field n, vectorNorm (L*ᵥ(U*ᵥg)) ≤ vectorNorm g) ∧
      (∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) := by
  obtain ⟨R,hR,hRR,hu⟩ := positive_sqrt_data (regularizedGram_posDef L hγ)
  have hi : R⁻¹.IsHermitian := by
    change (R⁻¹)ᵀ=R⁻¹
    rw [Matrix.transpose_nonsing_inv,show Rᵀ=R from hR.eq]
  refine ⟨R⁻¹,hi,?_,?_,?_,?_⟩
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact hu.inv
  · rw [← hRR]
    simp only [← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hu]
  · intro g
    have he := squareRoot_energy L R hR γ hRR (R⁻¹*ᵥg)
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec] at he
    exact (sq_le_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
      (by nlinarith [mul_nonneg hγ.le (sq_nonneg (vectorNorm (R⁻¹*ᵥg)))])
  · intro g
    have he := squareRoot_energy L R hR γ hRR (R⁻¹*ᵥg)
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec] at he
    apply (le_div_iff₀ (sqrt_pos.mpr hγ)).mpr
    apply (sq_le_sq₀ (mul_nonneg (vectorNorm_nonneg _) (sqrt_nonneg _)) (vectorNorm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hγ.le]
    nlinarith [sq_nonneg (vectorNorm (L*ᵥ(R⁻¹*ᵥg)))]

lemma symmetric_row_sq_bound {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ c*vectorNorm g) (i : Fin n) :
    ∑ k,U i k^2 ≤ c^2 := by
  let e : Field n := Pi.single i 1
  have he : vectorNorm e=1 := by
    apply (sq_eq_sq₀ (vectorNorm_nonneg _) zero_le_one).mp
    simp [vectorNorm_sq,vectorSqNorm,e,Pi.single_apply]
  have hx : U*ᵥe=fun k => U i k := by
    ext k
    simp only [e,Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col_apply]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_apply] using congrFun (congrFun hU.eq i) k
  have hh := hbound e
  rw [hx,he,mul_one] at hh
  simpa only [vectorNorm_sq,vectorSqNorm] using
    (sq_le_sq₀ (vectorNorm_nonneg _) hc).mpr hh

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
attribute [local irreducible] vectorNorm varianceAverage varianceLinear magnetizationRemainder tapField fieldJacobian magnetization

lemma vectorNorm_fourth_le {n : ℕ} (d : Field n) :
    vectorNorm d^4 ≤ (n:ℝ)*∑ i,d i^4 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1:ℝ)) (fun i => d i^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    ← pow_mul] at hc
  rw [show vectorNorm d^4=(vectorNorm d^2)^2 by ring,vectorNorm_sq]
  exact hc

lemma tap_remainder_sq {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y d : Field n) :
    vectorNorm (tapField j J h (y+d)-tapField j J h y-(fieldJacobian j J y)*ᵥd)^2 ≤
      (8*(j+K)^2+128*j^2)*∑ i,d i^4 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 ≤ ∑ i,d i^4 := Finset.sum_nonneg (fun i _ => by positivity)
  have h1 := tap_remainder_norm hn hj hK J hJ h y d
  have ha : 0 ≤ 2*(j+K)*sqrt (∑ i,d i^4) := by positivity
  have hb : 0 ≤ (8*j/sqrt (n:ℝ))*vectorNorm d^2 := by positivity
  have hsq := (sq_le_sq₀ (vectorNorm_nonneg _) (add_nonneg ha hb)).mpr h1
  have hcs : (2*(j+K)*sqrt (∑ i,d i^4)+(8*j/sqrt (n:ℝ))*vectorNorm d^2)^2 ≤
      2*(2*(j+K)*sqrt (∑ i,d i^4))^2+2*((8*j/sqrt (n:ℝ))*vectorNorm d^2)^2 := by
    nlinarith [sq_nonneg (2*(j+K)*sqrt (∑ i,d i^4)-(8*j/sqrt (n:ℝ))*vectorNorm d^2)]
  have he : 2*(2*(j+K)*sqrt (∑ i,d i^4))^2+2*((8*j/sqrt (n:ℝ))*vectorNorm d^2)^2=
      8*(j+K)^2*(∑ i,d i^4)+(128*j^2/(n:ℝ))*vectorNorm d^4 := by
    simp only [mul_pow,div_pow,Real.sq_sqrt hs,Real.sq_sqrt hn0.le]
    ring
  apply (hsq.trans hcs).trans
  rw [he]
  calc
    _ ≤ 8*(j+K)^2*(∑ i,d i^4)+(128*j^2/(n:ℝ))*((n:ℝ)*∑ i,d i^4) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (vectorNorm_fourth_le d) (by positivity))
    _ = _ := by field_simp

lemma varianceAverage_sq_difference {n : ℕ} (hn : 0 < n) (y d : Field n) :
    |varianceAverage (y+d)^2-varianceAverage y^2| ≤ 4/sqrt (n:ℝ)*vectorNorm d := by
  have hb := varianceAverage_bounds hn y
  have hb' := varianceAverage_bounds hn (y+d)
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg hb'.1 hb.1)]
  have hh := varianceAverage_difference hn y d
  calc
    _ ≤ 2*(2/sqrt (n:ℝ)*vectorNorm d) := mul_le_mul
      (show varianceAverage (y+d)+varianceAverage y ≤ 2 by linarith) hh
      (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_LocalGaussianMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal

lemma matrix_fourth_sum_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) :
    Integrable (fun g => ∑ i,((A*ᵥg) i)^4) (gaussianCoordinates κ) := by
  apply integrable_finsetSum
  intro i _
  exact linear_gaussian_fourth_integrable (A i)

lemma matrix_fourth_sum_mean {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) :
    (∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates κ)=3*∑ i,(∑ k,A i k^2)^2 := by
  simp only [Matrix.mulVec,dotProduct]
  rw [integral_finsetSum _ (fun i _ => linear_gaussian_fourth_integrable (A i)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact linear_gaussian_fourth (A i)

lemma matrix_fourth_sum_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i,∑ k,A i k^2 ≤ c) :
    (∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates (Fin m)) ≤ 3*(n:ℝ)*c^2 := by
  rw [matrix_fourth_sum_mean]
  have hs : (∑ i : Fin n,(∑ k,A i k^2)^2) ≤ ∑ _i : Fin n,c^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => sq_nonneg _)) hc).mpr (hb i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  nlinarith

lemma matrix_norm_fourth_integrable {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun g => vectorNorm (A*ᵥg)^4) (gaussianCoordinates (Fin m)) := by
  apply ((matrix_fourth_sum_integrable A).const_mul (n:ℝ)).mono' ?_ ?_
  · have he : (fun g => vectorNorm (A*ᵥg)^4)=fun g => (∑ i,((A*ᵥg) i)^2)^2 := by
      funext g
      rw [show vectorNorm (A*ᵥg)^4=(vectorNorm (A*ᵥg)^2)^2 by ring,vectorNorm_sq]
      rfl
    rw [he]
    fun_prop
  · filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact vectorNorm_fourth_le (A*ᵥg)

lemma matrix_norm_fourth_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i,∑ k,A i k^2 ≤ c) :
    (∫ g,vectorNorm (A*ᵥg)^4 ∂gaussianCoordinates (Fin m)) ≤ 3*(n:ℝ)^2*c^2 := by
  calc
    _ ≤ ∫ g,(n:ℝ)*(∑ i,((A*ᵥg) i)^4) ∂gaussianCoordinates (Fin m) :=
      integral_mono (matrix_norm_fourth_integrable A)
        ((matrix_fourth_sum_integrable A).const_mul _) (fun g => vectorNorm_fourth_le _)
    _ = (n:ℝ)*(∫ g,∑ i,((A*ᵥg) i)^4 ∂gaussianCoordinates (Fin m)) := integral_const_mul _ _
    _ ≤ (n:ℝ)*(3*(n:ℝ)*c^2) := mul_le_mul_of_nonneg_left (matrix_fourth_sum_bound A hc hb) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem localGaussian_fourth_moments {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ}
    (hU : U.IsHermitian) {γ σ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) :
    (∫ g,∑ i,((σ • U)*ᵥg) i^4 ∂gaussianCoordinates (Fin n)) ≤ 3*(n:ℝ)*σ^4/γ^2 ∧
    (∫ g,vectorNorm ((σ • U)*ᵥg)^4 ∂gaussianCoordinates (Fin n)) ≤ 3*(n:ℝ)^2*σ^4/γ^2 := by
  have hb (i : Fin n) : ∑ k,(σ • U) i k^2 ≤ σ^2/γ := by
    have hh := symmetric_row_sq_bound hU (inv_nonneg.mpr (sqrt_nonneg γ))
      (fun g => by simpa only [div_eq_mul_inv,mul_comm] using hbound g) i
    rw [inv_pow,Real.sq_sqrt hγ.le] at hh
    simp only [Matrix.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg σ)).trans_eq (by ring)
  have h1 := matrix_fourth_sum_bound (σ • U) (div_nonneg (sq_nonneg σ) hγ.le) hb
  have h2 := matrix_norm_fourth_bound (σ • U) (div_nonneg (sq_nonneg σ) hγ.le) hb
  constructor
  · convert h1 using 1; ring
  · convert h2 using 1; ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma gaussian_vectorSqNorm_integrable (n : ℕ) :
    Integrable (vectorSqNorm (n := n)) (gaussianCoordinates (Fin n)) := by
  have hh := (gaussianQuadratic_memLp (fun _ : Fin n => (1:ℝ))).integrable (by norm_num)
  change Integrable (fun g : Field n => ∑ i,1*g i^2) (gaussianCoordinates (Fin n)) at hh
  change Integrable (fun g : Field n => ∑ i,g i^2) (gaussianCoordinates (Fin n))
  simpa only [one_mul] using hh

lemma gaussian_vectorSqNorm_mean (n : ℕ) :
    (∫ g,vectorSqNorm g ∂gaussianCoordinates (Fin n))=(n:ℝ) := by
  simpa only [vectorSqNorm,gaussianQuadratic,one_mul,gaussianCoordinates,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using
    gaussianQuadratic_mean (fun _ : Fin n => (1:ℝ))

lemma localGaussianBall_measurable (n : ℕ) : MeasurableSet (localGaussianBall n) := by
  unfold localGaussianBall vectorSqNorm
  exact measurableSet_le (by fun_prop) measurable_const

lemma localGaussianBall_norm {n : ℕ} {g : Field n} (hg : g ∈ localGaussianBall n) :
    vectorNorm g ≤ 2*sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (by positivity)).mp
  rw [vectorNorm_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa only [localGaussianBall,Set.mem_ofPred_eq,show (2:ℝ)^2=4 by norm_num] using hg

theorem localGaussianBall_probability {n : ℕ} (hn : 0 < n) :
    3/4 ≤ (gaussianCoordinates (Fin n)).real (localGaussianBall n) := by
  let μ := gaussianCoordinates (Fin n)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all _ (fun g => vectorSqNorm_nonneg g))
    (gaussian_vectorSqNorm_integrable n) (4*(n:ℝ))
  rw [gaussian_vectorSqNorm_mean] at hh
  have hsub : (localGaussianBall n)ᶜ ⊆ {g | 4*(n:ℝ) ≤ vectorSqNorm g} := by
    intro g hg
    change ¬ vectorSqNorm g ≤ 4*(n:ℝ) at hg
    exact (lt_of_not_ge hg).le
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hc := probReal_compl_eq_one_sub (μ := μ) (localGaussianBall_measurable n)
  rw [hc] at hmono
  nlinarith

lemma localGaussianBall_ne_zero {n : ℕ} (hn : 0 < n) :
    gaussianCoordinates (Fin n) (localGaussianBall n) ≠ 0 := by
  intro he
  have hh := localGaussianBall_probability hn
  simp only [measureReal_def,he,ENNReal.toReal_zero] at hh
  norm_num at hh

lemma integrable_cond_of_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {s : Set Ω} {f : Ω → E}
    (hs : μ s ≠ 0) (hf : Integrable f μ) : Integrable f (cond μ s) := by
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hs)

lemma integral_cond_nonneg_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} {f : Ω → ℝ}
    (hp : 1/2 ≤ μ.real s)
    (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    (∫ x,f x ∂cond μ s) ≤ 2*∫ x,f x ∂μ := by
  have hps : 0 < μ.real s := by linarith
  have his : 0 ≤ ∫ x in s,f x ∂μ := integral_nonneg_of_ae (ae_restrict_of_ae hn)
  have hsle : (∫ x in s,f x ∂μ) ≤ ∫ x,f x ∂μ :=
    integral_mono_measure μ.restrict_le_self hn hf
  have hinv : (μ.real s)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hps).mpr (by linarith)
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv]
  change (μ.real s)⁻¹*(∫ x in s,f x ∂μ) ≤ _
  exact (mul_le_mul_of_nonneg_right hinv his).trans (mul_le_mul_of_nonneg_left hsle (by norm_num))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeEnergy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma continuous_vectorNorm (n : ℕ) : Continuous (vectorNorm (n := n)) := by
  unfold vectorNorm
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

lemma continuous_tapField {n : ℕ} (j : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    Continuous (tapField j J h) := by
  exact continuous_iff_continuousAt.mpr (fun y => (tapField_hasFDerivAt j J h y).continuousAt)

lemma tap_remainder_sq_integrable {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun g => vectorNorm (tapField j J h (y+A*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ(A*ᵥg))^2) (gaussianCoordinates (Fin n)) := by
  apply ((matrix_fourth_sum_integrable A).const_mul (8*(j+K)^2+128*j^2)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact ((continuous_vectorNorm n).comp
      (((continuous_tapField j J h).comp (by fun_prop)).sub continuous_const |>.sub (by fun_prop))).pow 2
  · filter_upwards [] with g
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact tap_remainder_sq hn hj hK J hJ h y (A*ᵥg)

theorem localGaussian_remainder_cond {n : ℕ} (hn : 0 < n) {j K : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsHermitian) {γ σ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ) :
    (∫ g,vectorNorm (tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg))^2
      ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) ≤
      6*(8*(j+K)^2+128*j^2)*(n:ℝ)*σ^4/γ^2 := by
  let C := 8*(j+K)^2+128*j^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := tap_remainder_sq_integrable hn hj hK J hJ h y (σ • U)
  have hp : 1/2 ≤ (gaussianCoordinates (Fin n)).real (localGaussianBall n) :=
    (by norm_num : (1:ℝ)/2 ≤ 3/4).trans (localGaussianBall_probability hn)
  have hc := integral_cond_nonneg_le_two hp hi (ae_of_all _ (fun g => sq_nonneg _))
  have hb : (∫ g,vectorNorm (tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
      (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg))^2 ∂gaussianCoordinates (Fin n)) ≤
      C*(3*(n:ℝ)*σ^4/γ^2) := by
    calc
      _ ≤ ∫ g,C*(∑ i,(((σ • U)*ᵥg) i)^4) ∂gaussianCoordinates (Fin n) :=
        integral_mono hi ((matrix_fourth_sum_integrable _).const_mul _)
          (fun g => tap_remainder_sq hn hj hK J hJ h y _)
      _ = C*(∫ g,∑ i,(((σ • U)*ᵥg) i)^4 ∂gaussianCoordinates (Fin n)) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (localGaussian_fourth_moments hU hγ hbound).1 hC
  calc
    _ ≤ 2*(C*(3*(n:ℝ)*σ^4/γ^2)) := hc.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by dsimp [C]; ring

lemma vectorNorm_add_sq_young {n : ℕ} (u v : Field n) {η : ℝ} (hη : 0 < η) :
    vectorNorm (u+v)^2 ≤ (1+η)*vectorNorm u^2+(1+η⁻¹)*vectorNorm v^2 := by
  have hh := (sq_le_sq₀ (vectorNorm_nonneg _) (add_nonneg (vectorNorm_nonneg u)
    (vectorNorm_nonneg v))).mpr (vectorNorm_add_le u v)
  have hy : 2*vectorNorm u*vectorNorm v ≤ η*vectorNorm u^2+η⁻¹*vectorNorm v^2 := by
    apply (mul_le_mul_iff_right₀ hη).mp
    have he : η⁻¹*η=1 := inv_mul_cancel₀ hη.ne'
    nlinarith [sq_nonneg (η*vectorNorm u-vectorNorm v)]
  nlinarith

theorem local_energy_pointwise {n : ℕ} (u v R g : Field n) {σ η ρ : ℝ}
    (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (hu : vectorNorm u ≤ ρ*sqrt (n:ℝ))
    (hv : vectorNorm v ≤ σ*vectorNorm g) (hg : g ∈ localGaussianBall n) :
    vectorNorm g^2/2-vectorNorm (u+v+R)^2/(2*σ^2) ≥
      -2*η*(n:ℝ)-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2)/σ^2 := by
  have hsσ : 0 < σ^2 := sq_pos_of_pos hσ
  have hu2 := (sq_le_sq₀ (vectorNorm_nonneg u) (by positivity)).mpr hu
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hu2
  have hv2 := (sq_le_sq₀ (vectorNorm_nonneg v) (mul_nonneg hσ.le (vectorNorm_nonneg g))).mpr hv
  rw [mul_pow] at hv2
  have hUR := vectorNorm_add_sq_young u R (η := 1) (by norm_num)
  norm_num only [inv_one,one_add_one_eq_two] at hUR
  have hh := vectorNorm_add_sq_young v (u+R) hη
  have he : v+(u+R)=u+v+R := by abel
  rw [he] at hh
  have hpos : 0 ≤ 1+η⁻¹ := by positivity
  have hcombine : vectorNorm (u+v+R)^2 ≤ (1+η)*σ^2*vectorNorm g^2+
      2*(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2) := by
    calc
      _ ≤ (1+η)*vectorNorm v^2+(1+η⁻¹)*(2*vectorNorm u^2+2*vectorNorm R^2) :=
        hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hUR hpos))
      _ ≤ (1+η)*(σ^2*vectorNorm g^2)+(1+η⁻¹)*(2*(ρ^2*(n:ℝ))+2*vectorNorm R^2) :=
        add_le_add (mul_le_mul_of_nonneg_left hv2 (by positivity))
          (mul_le_mul_of_nonneg_left (by linarith) hpos)
      _ = _ := by ring
  have hgn : vectorNorm g^2 ≤ 4*(n:ℝ) := by rw [vectorNorm_sq]; exact hg
  apply (mul_le_mul_iff_right₀ hsσ).mp
  have he1 : (-2*η*(n:ℝ)-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2)/σ^2)*σ^2=
      -2*η*(n:ℝ)*σ^2-(1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm R^2) := by
    rw [sub_mul,div_mul_cancel₀ _ hsσ.ne']
  have he2 : (vectorNorm g^2/2-vectorNorm (u+v+R)^2/(2*σ^2))*σ^2=
      (σ^2*vectorNorm g^2-vectorNorm (u+v+R)^2)/2 := by
    field_simp
  rw [mul_comm (σ^2) _,mul_comm (σ^2) _,he1,he2]
  nlinarith [mul_le_mul_of_nonneg_left hgn (mul_nonneg hη.le hsσ.le)]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma localGaussianBall_compact (n : ℕ) : IsCompact (localGaussianBall n) := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin n => -2*sqrt (n:ℝ)) (fun _ : Fin n => 2*sqrt (n:ℝ)))).of_isClosed_subset
  · apply isClosed_le _ continuous_const
    unfold vectorSqNorm
    fun_prop
  · intro g hg
    have hb := localGaussianBall_norm hg
    have hc (i : Fin n) : |g i| ≤ 2*sqrt (n:ℝ) := by
      have hh := PiLp.norm_apply_le (WithLp.toLp 2 g) i
      exact (show |g i| ≤ vectorNorm g by simpa only [Real.norm_eq_abs,vectorNorm] using hh).trans hb
    exact ⟨fun i => by simpa only [neg_mul] using (abs_le.mp (hc i)).1,fun i => (abs_le.mp (hc i)).2⟩

lemma localGaussian_cond_integrable {n : ℕ} (hn : 0 < n) {f : Field n → ℝ}
    (hf : Continuous f) : Integrable f (cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) := by
  exact (hf.continuousOn.integrableOn_compact (localGaussianBall_compact n)).smul_measure
    (ENNReal.inv_ne_top.mpr (localGaussianBall_ne_zero hn))

lemma localExponent_continuous {n : ℕ} (j σ : ℝ) (J U : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    Continuous (localExponent j σ J U h y) := by
  have hb : Continuous (varianceAverage (n := n)) := by
    unfold varianceAverage
    exact continuous_const.sub (continuous_iff_continuousAt.mpr (fun y => (overlap_hasFDerivAt y).continuousAt))
  exact (((continuous_vectorNorm n).pow 2 |>.div_const 2).sub
    (((continuous_vectorNorm n).comp ((continuous_tapField j J h).comp (by fun_prop))).pow 2 |>.div_const _)).add
      (((hb.comp (by fun_prop)).pow 2 |>.const_mul ((n:ℝ)*j)).div_const 2)

lemma localGaussian_displacement {n : ℕ} {U : Matrix (Fin n) (Fin n) ℝ} {γ σ : ℝ}
    (_hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    {g : Field n} (hg : g ∈ localGaussianBall n) :
    vectorNorm ((σ • U)*ᵥg) ≤ (2*σ/sqrt γ)*sqrt (n:ℝ) := by
  rw [Matrix.smul_mulVec]
  change vectorNorm (fun i => σ*(U*ᵥg) i) ≤ _
  rw [vectorNorm_smul,abs_of_nonneg hσ]
  calc
    _ ≤ σ*(vectorNorm g/sqrt γ) := mul_le_mul_of_nonneg_left (hbound g) hσ
    _ ≤ σ*((2*sqrt (n:ℝ))/sqrt γ) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (localGaussianBall_norm hg) (sqrt_nonneg _)) hσ
    _ = _ := by ring

lemma localGaussian_variance_change {n : ℕ} (hn : 0 < n) (y : Field n)
    {U : Matrix (Fin n) (Fin n) ℝ} {γ σ : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    {g : Field n} (hg : g ∈ localGaussianBall n) :
    |varianceAverage (y+(σ • U)*ᵥg)^2-varianceAverage y^2| ≤ 8*σ/sqrt γ := by
  have hn0 : sqrt (n:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ 4/sqrt (n:ℝ)*vectorNorm ((σ • U)*ᵥg) := varianceAverage_sq_difference hn y _
    _ ≤ 4/sqrt (n:ℝ)*((2*σ/sqrt γ)*sqrt (n:ℝ)) := mul_le_mul_of_nonneg_left
      (localGaussian_displacement hγ hσ hbound hg) (by positivity)
    _ = _ := by field_simp; ring

theorem localGaussian_exponent_bound {n : ℕ} (hn : 0 < n) {j K γ σ η ρ : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hγ : 0 < γ) (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (J U : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    (hU : U.IsHermitian)
    (hbound : ∀ g : Field n, vectorNorm (U*ᵥg) ≤ vectorNorm g/sqrt γ)
    (hlin : ∀ g : Field n, vectorNorm ((fieldJacobian j J y)*ᵥ(U*ᵥg)) ≤ vectorNorm g)
    (hres : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ)) :
    (n:ℝ)*(j*varianceAverage y^2/2-2*η-
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)-4*j*σ/sqrt γ) ≤
      ∫ g,localExponent j σ J U h y g
        ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n) := by
  let μ := cond (gaussianCoordinates (Fin n)) (localGaussianBall n)
  let : IsProbabilityMeasure μ := cond_isProbabilityMeasure (localGaussianBall_ne_zero hn)
  let R : Field n → Field n := fun g => tapField j J h (y+(σ • U)*ᵥg)-tapField j J h y-
    (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg)
  have hiR : Integrable (fun g => vectorNorm (R g)^2) μ :=
    integrable_cond_of_integrable (localGaussianBall_ne_zero hn)
      (tap_remainder_sq_integrable hn hj hK J hJ h y _)
  have hR := localGaussian_remainder_cond hn hj hK J hJ h y hU hγ hbound (σ := σ)
  change (∫ g,vectorNorm (R g)^2 ∂μ) ≤ _ at hR
  let f : Field n → ℝ := fun g => (n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
    (1+η⁻¹)*(ρ^2*(n:ℝ)+vectorNorm (R g)^2)/σ^2-4*(n:ℝ)*j*σ/sqrt γ
  have hif : Integrable f μ := by
    exact (((integrable_const _).sub (integrable_const _)).sub
      (((integrable_const _).add hiR).const_mul _ |>.div_const _)).sub (integrable_const _)
  have hmono : (∫ g,f g ∂μ) ≤ ∫ g,localExponent j σ J U h y g ∂μ := by
    apply integral_mono_ae hif (localGaussian_cond_integrable hn (localExponent_continuous _ _ _ _ _ _))
    apply ae_cond_of_forall_mem (localGaussianBall_measurable n)
    intro g hg
    let v := (fieldJacobian j J y)*ᵥ((σ • U)*ᵥg)
    have hv : vectorNorm v ≤ σ*vectorNorm g := by
      dsimp [v]
      rw [Matrix.smul_mulVec,Matrix.mulVec_smul]
      change vectorNorm (fun i => σ*((fieldJacobian j J y)*ᵥ(U*ᵥg)) i) ≤ _
      rw [vectorNorm_smul,abs_of_pos hσ]
      exact mul_le_mul_of_nonneg_left (hlin g) hσ.le
    have hh := local_energy_pointwise (tapField j J h y) v (R g) g hσ hη hρ hres hv hg
    have he : tapField j J h y+v+R g=tapField j J h (y+(σ • U)*ᵥg) := by dsimp [v,R]; abel
    rw [he] at hh
    have hb := (abs_le.mp (localGaussian_variance_change hn y hγ hσ.le hbound hg)).1
    have hbj := mul_le_mul_of_nonneg_left hb (show 0 ≤ (n:ℝ)*j/2 by positivity)
    dsimp [f,localExponent]
    ring_nf at hh hbj ⊢
    linarith only [hh,hbj]
  have he : (∫ g,f g ∂μ)=(n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
      (1+η⁻¹)*(ρ^2*(n:ℝ)+∫ g,vectorNorm (R g)^2 ∂μ)/σ^2-4*(n:ℝ)*j*σ/sqrt γ := by
    have hfEq : f=fun g => ((n:ℝ)*j*varianceAverage y^2/2-2*η*(n:ℝ)-
        (1+η⁻¹)*ρ^2*(n:ℝ)/σ^2-4*(n:ℝ)*j*σ/sqrt γ)-
        ((1+η⁻¹)/σ^2)*vectorNorm (R g)^2 := by
      funext g
      dsimp [f]
      ring
    rw [hfEq,integral_sub (integrable_const _) (hiR.const_mul _),integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
    ring
  rw [he] at hmono
  apply le_trans ?_ hmono
  have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ (1+η⁻¹)/σ^2 by positivity)
  have hsσ : σ ≠ 0 := hσ.ne'
  have heq : (1+η⁻¹)*(ρ^2*(n:ℝ)+6*(8*(j+K)^2+128*j^2)*(n:ℝ)*σ^4/γ^2)/σ^2=
      (n:ℝ)*(1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2) := by
    field_simp
  ring_nf at hh heq ⊢
  linarith only [hh,heq]

theorem localGaussian_jensen {n : ℕ} (hn : 0 < n) (j σ : ℝ)
    (J U : Matrix (Fin n) (Fin n) ℝ) (h y : Field n) :
    exp (∫ g,localExponent j σ J U h y g ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n)) ≤
      ∫ g,exp (localExponent j σ J U h y g) ∂cond (gaussianCoordinates (Fin n)) (localGaussianBall n) := by
  let := cond_isProbabilityMeasure (localGaussianBall_ne_zero hn)
  exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _))
    (localGaussian_cond_integrable hn (localExponent_continuous _ _ _ _ _ _))
    (localGaussian_cond_integrable hn (continuous_exp.comp (localExponent_continuous _ _ _ _ _ _)))

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeChange
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma map_affine_matrix_volume {n : ℕ} (y : Field n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) :
    Measure.map (fun g : Field n => y+A*ᵥg) volume = ENNReal.ofReal |A.det⁻¹| • volume := by
  have he : (fun g : Field n => y+A*ᵥg) = (fun z => y+z) ∘ (fun g => A*ᵥg) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop)]
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  change Measure.map (fun g => A*ᵥg) volume=_ at hm
  rw [hm,Measure.map_smul,map_add_left_eq_self]

lemma affine_set_lintegral_le {n : ℕ} (y : Field n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) {B E : Set (Field n)} (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBE : ∀ g ∈ B,y+A*ᵥg ∈ E) (f : Field n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g in B,f (y+A*ᵥg)) ≤ ENNReal.ofReal |A.det⁻¹| * ∫⁻ z in E,f z := by
  calc
    _ = ∫⁻ g,(B.indicator (fun g => f (y+A*ᵥg))) g := (lintegral_indicator hB _).symm
    _ ≤ ∫⁻ g,(E.indicator f) (y+A*ᵥg) := by
      apply lintegral_mono
      intro g
      by_cases hg : g ∈ B
      · simp only [indicator_of_mem hg, indicator_of_mem (hBE g hg),le_refl]
      · rw [indicator_of_notMem hg]
        exact bot_le
    _ = ∫⁻ z,E.indicator f z ∂Measure.map (fun g : Field n => y+A*ᵥg) volume :=
      (lintegral_map (hf.indicator hE) (by fun_prop)).symm
    _ = _ := by rw [map_affine_matrix_volume y A hA,lintegral_smul_measure,lintegral_indicator hE]; rfl

lemma gaussian_standard_density {n : ℕ} : gaussianCoordinates (Fin n) =
    (volume : Measure (Field n)).withDensity (fun g =>
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^(n:ℕ)*exp (-vectorNorm g^2/2))) := by
  rw [gaussianCoordinates,GaussianDensity.pi_gaussian_density (hv := fun _ => one_ne_zero)]
  congr 1
  funext g
  congr 1
  simp only [gaussianPDFReal,sub_zero,NNReal.coe_one,mul_one,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← exp_sum,← Finset.sum_div,
    ← Finset.sum_neg_distrib,vectorNorm_sq,vectorSqNorm]

lemma gaussian_tilt_cancellation {n : ℕ} {B : Set (Field n)} (hB : MeasurableSet B)
    (φ : Field n → ℝ) (hφ : Measurable φ) :
    (∫⁻ g in B,ENNReal.ofReal (exp (vectorNorm g^2/2+φ g)) ∂gaussianCoordinates (Fin n)) =
    ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n) * ∫⁻ g in B,ENNReal.ofReal (exp (φ g)) := by
  have hnorm : Measurable (vectorNorm (n := n)) := (continuous_vectorNorm n).measurable
  rw [gaussian_standard_density,restrict_withDensity hB,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have he (g : Field n) :
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n*exp (-vectorNorm g^2/2)) *
        ENNReal.ofReal (exp (vectorNorm g^2/2+φ g)) =
      ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n) * ENNReal.ofReal (exp (φ g)) := by
    rw [← ENNReal.ofReal_mul (by positivity),mul_assoc,← exp_add]
    have hh : -vectorNorm g^2/2+(vectorNorm g^2/2+φ g)=φ g := by ring
    rw [hh,ENNReal.ofReal_mul (by positivity)]
  simp_rw [Pi.mul_apply,he]
  exact lintegral_const_mul _ (by fun_prop)

theorem local_volume_change_of_variables {n : ℕ} (y : Field n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U.det ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    {B E : Set (Field n)} (hB : MeasurableSet B) (hE : MeasurableSet E)
    (hBE : ∀ g ∈ B,y+(σ • U)*ᵥg ∈ E) (φ : Field n → ℝ) (hφ : Measurable φ) :
    ENNReal.ofReal |U.det| *
      (∫⁻ g in B,ENNReal.ofReal (exp (vectorNorm g^2/2+φ (y+(σ • U)*ᵥg)))
        ∂gaussianCoordinates (Fin n)) ≤
    ENNReal.ofReal (((sqrt (2*Real.pi)*σ)⁻¹)^n) * ∫⁻ z in E,ENNReal.ofReal (exp (φ z)) := by
  have hA : (σ • U).det ≠ 0 := by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hσ.ne') hU
  rw [gaussian_tilt_cancellation hB (fun g => φ (y+(σ • U)*ᵥg)) (hφ.comp (by fun_prop))]
  have hh := affine_set_lintegral_le y (σ • U) hA hB hE hBE (fun z => ENNReal.ofReal (exp (φ z))) (by fun_prop)
  calc
    _ ≤ ENNReal.ofReal |U.det| * (ENNReal.ofReal (((sqrt (2*Real.pi))⁻¹)^n)*
        (ENNReal.ofReal |(σ • U).det⁻¹| * ∫⁻ z in E,ENNReal.ofReal (exp (φ z)))) := by gcongr
    _ = _ := by
      rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Matrix.det_smul,Fintype.card_fin,abs_inv,abs_mul,abs_pow,abs_of_pos hσ,mul_inv]
      have hUd : |U.det| ≠ 0 := abs_ne_zero.mpr hU
      rw [mul_inv,mul_pow]
      simp only [← inv_pow]
      field_simp

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma conditional_lintegral_identity {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {B : Set Ω} (hB : μ B ≠ 0) (f : Ω → ℝ≥0∞) :
    μ B*(∫⁻ x,f x ∂cond μ B)=∫⁻ x in B,f x ∂μ := by
  rw [ProbabilityTheory.cond,lintegral_smul_measure]
  change μ B*((μ B)⁻¹*(∫⁻ x in B,f x ∂μ))=_
  rw [← mul_assoc,ENNReal.mul_inv_cancel hB (measure_ne_top _ _),one_mul]

lemma whitening_logdet {n : ℕ} (U Q : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.det ≠ 0) (hQ : 0 < Q.det) (he : U*Q*U=1) :
    log |U.det| = -log Q.det/2 := by
  have hd : |U.det|^2*Q.det=1 := by
    have hh := congrArg Matrix.det he
    rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_one] at hh
    rw [sq_abs]
    nlinarith only [hh]
  have hh := congrArg log hd
  rw [log_mul (pow_ne_zero _ (abs_ne_zero.mpr hU)) hQ.ne',log_pow,log_one] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma localAction_continuous {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Field n) : Continuous (localAction j σ J h) := by
  have hb : Continuous (varianceAverage (n := n)) := by
    unfold varianceAverage
    exact continuous_const.sub (continuous_iff_continuousAt.mpr (fun y => (overlap_hasFDerivAt y).continuousAt))
  exact (((continuous_vectorNorm n).comp (continuous_tapField j J h)).pow 2 |>.neg |>.div_const _).add
    ((hb.pow 2 |>.const_mul _).div_const _)

theorem local_volume_quantitative {n : ℕ} (hn : 0 < n) {j K γ σ η ρ r ε₁ : ℝ}
    (hj : 0 ≤ j) (hK : 0 ≤ K) (hγ : 0 < γ) (hσ : 0 < σ) (hη : 0 < η) (hρ : 0 ≤ ρ)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ z : Field n, vectorNorm (J*ᵥz) ≤ K*vectorNorm z) (h y : Field n)
    {E : Set (Field n)} (hE : MeasurableSet E)
    (hball : ∀ d : Field n,vectorNorm d ≤ r*sqrt (n:ℝ) → y+d ∈ E)
    (hsmall : 2*σ/sqrt γ ≤ r)
    (hdet : log ((fieldJacobian j J y)ᵀ*(fieldJacobian j J y)+γ • 1).det ≤
      (n:ℝ)*(j*varianceAverage y^2+ε₁))
    (hres : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ)) :
    ENNReal.ofReal ((3/4:ℝ)*exp (-(n:ℝ)*(ε₁/2+2*η+
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ))) ≤
      localVolume j σ J h E := by
  let L := fieldJacobian j J y
  let Q := Lᵀ*L+γ • (1 : Matrix (Fin n) (Fin n) ℝ)
  obtain ⟨U,hUH,hUd,hUQ,hlin,hbound⟩ := localGaussian_whitening L hγ
  have hU : U.det ≠ 0 := isUnit_iff_ne_zero.mp hUd
  have hQ : 0 < Q.det := (regularizedGram_posDef L hγ).det_pos
  have hlog := whitening_logdet U Q hU hQ hUQ
  let μ := gaussianCoordinates (Fin n)
  let B := localGaussianBall n
  let l : ℝ := j*varianceAverage y^2/2-2*η-
    (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)-4*j*σ/sqrt γ
  have hjensen : exp ((n:ℝ)*l) ≤ ∫ g,exp (localExponent j σ J U h y g) ∂cond μ B := by
    exact (exp_le_exp.mpr (localGaussian_exponent_bound hn hj hK hγ hσ hη hρ
      J U hJ h y hUH hbound hlin hres)).trans (localGaussian_jensen hn j σ J U h y)
  have hp : ENNReal.ofReal (3/4:ℝ) ≤ μ B := by
    have hh := ENNReal.ofReal_le_ofReal (localGaussianBall_probability hn)
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have hcond : ENNReal.ofReal (exp ((n:ℝ)*l)) ≤
      ∫⁻ g,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂cond μ B := by
    have hi : Integrable (fun g => exp (localExponent j σ J U h y g)) (cond μ B) :=
      localGaussian_cond_integrable hn (continuous_exp.comp (localExponent_continuous _ _ _ _ _ _))
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => (exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal hjensen
  have hvol := local_volume_change_of_variables y U hU hσ (localGaussianBall_measurable n) hE
    (fun g hg => hball _ ((localGaussian_displacement hγ hσ.le hbound hg).trans
      (mul_le_mul_of_nonneg_right hsmall (sqrt_nonneg _))))
    (localAction j σ J h) (localAction_continuous _ _ _ _).measurable
  have hexp (g : Field n) : vectorNorm g^2/2+localAction j σ J h (y+(σ • U)*ᵥg)=
      localExponent j σ J U h y g := by unfold localAction localExponent; ring
  simp_rw [hexp] at hvol
  change ENNReal.ofReal |U.det| *(∫⁻ g in B,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂μ) ≤
    localVolume j σ J h E at hvol
  rw [← conditional_lintegral_identity (localGaussianBall_ne_zero hn)] at hvol
  have hscalar : (3/4:ℝ)*exp (-(n:ℝ)*(ε₁/2+2*η+
      (1+η⁻¹)*(ρ^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ)) ≤
      |U.det| *((3/4:ℝ)*exp ((n:ℝ)*l)) := by
    rw [← exp_log (abs_pos.mpr hU)]
    calc
      _ ≤ (3/4:ℝ)*exp (log |U.det|+(n:ℝ)*l) := by
        apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
        rw [hlog]
        change log Q.det ≤ _ at hdet
        dsimp [l]
        linarith only [hdet]
      _ = _ := by rw [exp_add]; ring
  calc
    _ ≤ ENNReal.ofReal (|U.det| *((3/4:ℝ)*exp ((n:ℝ)*l))) := ENNReal.ofReal_le_ofReal hscalar
    _ = ENNReal.ofReal |U.det| *(ENNReal.ofReal (3/4:ℝ)*ENNReal.ofReal (exp ((n:ℝ)*l))) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal |U.det| *(μ B*(∫⁻ g,ENNReal.ofReal (exp (localExponent j σ J U h y g)) ∂cond μ B)) := by
      gcongr
    _ ≤ _ := hvol

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldIntegralReduction
attribute [-instance] _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal
attribute [local fun_prop] continuous_radialDensity

lemma continuous_fieldMollifier {n : ℕ} (j σ : ℝ) :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × (Fin n → ℝ))=>
      fieldMollifier j σ p.1 p.2.1 p.2.2) := by
  unfold fieldMollifier tapField onsager overlap magnetization
  exact ((continuous_radialDensity σ).comp (by fun_prop)).mul (by fun_prop)

lemma field_noise_convolution {n : ℕ} [NeZero n] {j t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ)
    (y : Fin n → ℝ) (f : ((Fin n×Fin n) → ℝ) → ℝ≥0∞) (g : MatrixCoordinates (Fin n) → ℝ) :
      (∫⁻ x, ENNReal.ofReal (fieldMollifier j σ
        (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) (fun i=>t+x i) y)*
        f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)
        ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))=
      ENNReal.ofReal (exp ((n:ℝ)*j*(1-overlap y)^2/2))*
        (ENNReal.ofReal (radialDensity (sqrt (t+σ^2))
          (empiricalObservation j t σ y-goeMatrix (j/(n:ℝ)) g*ᵥmagnetization y))*
            f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)) := by
    simp only [fieldMollifier,tapField_planted_observation j t σ,
      ENNReal.ofReal_mul (radialDensity_pos hσ _).le]
    rw [lintegral_mul_const _ (by fun_prop),lintegral_mul_const _ (by fun_prop),gaussian_radial_convolution ht hσ]
    ring

theorem field_reduction_fixed {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) (y : Fin n → ℝ) :
    (∫⁻ g, ∫⁻ x, ENNReal.ofReal (fieldMollifier j σ
        (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) (fun i=>t+x i) y)*
        E.indicator (fun _=>1) ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=
    ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
      conditionalFieldWeight j t σ E y := by
  let f : ((Fin n×Fin n) → ℝ) → ℝ≥0∞ := fun W=>E.indicator (fun _=>1) (W,y)
  have hf : Measurable f := measurable_const.indicator (hE.preimage (by fun_prop))
  change (∫⁻ g, ∫⁻ x, ENNReal.ofReal (fieldMollifier j σ _ _ y)*f _ ∂_ ∂_)=_
  simp_rw [field_noise_convolution ht hσ y f]
  have hgf : Measurable (fun g : MatrixCoordinates (Fin n) → ℝ => f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)) := hf.comp (by unfold goeMatrix; fun_prop)
  have hgr : Measurable (fun g : MatrixCoordinates (Fin n) → ℝ => ENNReal.ofReal
      (radialDensity (sqrt (t+σ^2)) (empiricalObservation j t σ y-goeMatrix (j/(n:ℝ)) g*ᵥmagnetization y))) := by
    apply Measurable.ennreal_ofReal
    apply (continuous_radialDensity _).measurable.comp
    unfold Matrix.mulVec dotProduct goeMatrix
    fun_prop
  erw [lintegral_const_mul _ (hgr.mul hgf),goe_pointwise_conditional_integral
    (div_nonneg hj (Nat.cast_nonneg n)) (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) _ _ f hf]
  have hfi : (∫⁻ W,f W ∂conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y)
      (empiricalObservation j t σ y))=conditionalFieldWeight j t σ E y := by
    change (∫⁻ W, {W | (W,y)∈E}.indicator (fun _=>(1 : ℝ≥0∞)) W ∂_)=_
    have hset : MeasurableSet {W : (Fin n×Fin n) → ℝ | (W,y)∈E} := hE.preimage (by fun_prop)
    rw [lintegral_indicator hset,lintegral_const]
    simp [conditionalFieldWeight]
  rw [hfi,← mul_assoc,← ENNReal.ofReal_mul (exp_pos _).le]
  congr 1
  congr 1
  rw [mul_comm,scalar_density_cancellation hj ht hσ y]
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators ENNReal

lemma fieldMollifier_eq_localAction {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h y : Field n) : fieldMollifier j σ J h y=
      ((sqrt (2*Real.pi)*σ)⁻¹)^n*exp (localAction j σ J h y) := by
  unfold fieldMollifier radialDensity localAction varianceAverage
  rw [Fintype.card_fin,vectorNorm_sq,mul_assoc,← exp_add]
  simp only [vectorSqNorm,dotProduct,pow_two]

lemma fieldIntegral_eq_localVolume {n : ℕ} {σ : ℝ} (hσ : 0 < σ) (j : ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) (E : Set (Field n)) :
    fieldIntegral j σ J h E=localVolume j σ J h E := by
  unfold fieldIntegral localVolume
  simp_rw [fieldMollifier_eq_localAction,ENNReal.ofReal_mul (by positivity : 0 ≤ ((sqrt (2*Real.pi)*σ)⁻¹)^n)]
  exact lintegral_const_mul _ (Real.measurable_exp.comp (localAction_continuous j σ J h).measurable |>.ennreal_ofReal)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalIntegralRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma measurableSet_badFieldFlat (n : ℕ) (j A ε m : ℝ) :
    MeasurableSet (badFieldFlat n j A ε m) :=
  ((isClosed_badFieldSet n j A ε m).preimage (by fun_prop)).measurableSet

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldTonelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma fieldIntegral_indicator {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    fieldIntegral j σ J h E=∫⁻ y, ENNReal.ofReal (fieldMollifier j σ J h y)*E.indicator (fun _=>1) y := by
  rw [fieldIntegral,← lintegral_indicator hE]
  apply lintegral_congr
  intro y
  by_cases hy : y∈E <;> simp [hy]

theorem field_integral_gaussian_reduction {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) :
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=
    ∫⁻ y, ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
      conditionalFieldWeight j t σ E y := by
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let H : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p=>ENNReal.ofReal (fieldMollifier j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1))
      (fun i=>t+p.1.2 i) p.2)* E.indicator (fun _=>1) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)
  have hsJ : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1)) :=
    ((goeMatrix_pi_lipschitz (j/(n:ℝ))).continuous.comp (continuous_fst.comp continuous_fst)).add continuous_const
  have htime : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (fun i=>t+p.1.2 i)) := by
    apply continuous_pi
    intro i
    exact continuous_const.add ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1),((fun i=>t+p.1.2 i),p.2))) :=
    hsJ.prodMk (htime.prodMk continuous_snd)
  have hφ := ((continuous_fieldMollifier j σ).comp hmap).measurable.ennreal_ofReal
  have hI : Measurable (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      E.indicator (fun _=>(1 : ℝ≥0∞)) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)) := by
    apply (measurable_const.indicator hE).comp
    unfold goeMatrix
    fun_prop
  have hH : Measurable H := hφ.mul hI
  have he (g : MatrixCoordinates (Fin n) → ℝ) (x : Fin n → ℝ) :
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E}=
      ∫⁻ y,H ((g,x),y) := by
    have hs : MeasurableSet {y : Fin n → ℝ | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E} := hE.preimage (by fun_prop)
    erw [fieldIntegral_indicator _ _ _ _ _ hs]
    apply lintegral_congr
    intro y
    dsimp [H]
    by_cases hy : ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E <;> simp [hy]
  simp_rw [he]
  change (∫⁻ g,∫⁻ x,∫⁻ y,H ((g,x),y) ∂volume ∂ν ∂μ)=_
  rw [← lintegral_prod _ hH.lintegral_prod_right'.aemeasurable,
    lintegral_lintegral_swap hH.aemeasurable]
  apply lintegral_congr
  intro y
  have hh : Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ) => H (p,y)) := hH.comp (by fun_prop)
  rw [lintegral_prod _ hh.aemeasurable]
  exact field_reduction_fixed hj ht hσ E hE y
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_BadIntegralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem positive_time_bad_integral {j A t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
    ∃ m ε σ₀ a : ℝ,0 < m ∧ 0 < ε ∧ 0 < σ₀ ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n],N ≤ n → ∀ t ∈ Icc t₀ T,∀ σ ∈ Ioc 0 σ₀,
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | (goeMatrix (j/(n:ℝ)) g,y)∈badFieldSet n j A ε m}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨m,ε,σ₀,a,hm,hε,hσ₀,ha,N,hN⟩ := conditional_bad_integral_rate hj hj1 hA hsub ht₀ hT
  refine ⟨m,ε,σ₀,a,hm,hε,hσ₀,ha,N,?_⟩
  intro n _ hn t ht σ hσ
  have hh := field_integral_gaussian_reduction hj.le (ht₀.le.trans ht.1) hσ.1
    (badFieldFlat n j A ε m) (measurableSet_badFieldFlat _ _ _ _ _)
  change _=∫⁻ y,reducedBadDensity j t σ A ε m y at hh
  erw [hh]
  exact hN n hn t ht σ hσ
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeFull
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set Filter
open scoped BigOperators ENNReal NNReal

lemma nonnegative_continuous_small {f : ℝ → ℝ} (hf : ContinuousAt f 0) (hzero : f 0=0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ,0 < δ ∧ ∀ x : ℝ,0 ≤ x → x < δ → f x < ε := by
  have hh : ∀ᶠ x in nhds (0:ℝ), f x < ε :=
    hf.tendsto.eventually_lt_const (by rw [hzero]; exact hε)
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨δ,hδ,fun x hx hxd => hnear ?_⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hx] using hxd

lemma absorb_three_quarters_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ,N ≤ n →
      exp (-ε*(n:ℝ)) ≤ (3/4:ℝ)*exp (-(3*ε/4)*(n:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (4/ε)
  refine ⟨max N 1,by omega,?_⟩
  intro n hn
  have hnn : 4/ε ≤ (n:ℝ) := hN.trans (by exact_mod_cast (le_trans (le_max_left N 1) hn))
  have hx : 1 ≤ ε*(n:ℝ)/4 := by
    have hh := (div_le_iff₀ hε).mp hnn
    nlinarith
  have he : exp (-(ε*(n:ℝ)/4)) ≤ 3/4 := by
    rw [exp_neg,inv_eq_one_div,div_le_iff₀ (exp_pos _)]
    have hh := add_one_le_exp (ε*(n:ℝ)/4)
    nlinarith only [hh,hx]
  have hsplit : -ε*(n:ℝ)=-(ε*(n:ℝ)/4)+(-(3*ε/4)*(n:ℝ)) := by ring
  rw [hsplit,exp_add]
  exact mul_le_mul_of_nonneg_right he (exp_pos _).le

theorem local_volume_uniform {j K r ε : ℝ} (hj : 0 ≤ j) (hK : 0 ≤ K)
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ ε₁ : ℝ,0 < ε₁ ∧ ∀ γ : ℝ,0 < γ →
    ∃ σ₀ : ℝ,0 < σ₀ ∧ ∀ σ : ℝ,0 < σ → σ < σ₀ →
    ∃ ρ : ℝ,0 < ρ ∧ ∃ N : ℕ,0 < N ∧ ∀ n,N ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) ℝ,
    (∀ z : Field n,vectorNorm (J*ᵥz) ≤ K*vectorNorm z) →
    ∀ h y : Field n,∀ E : Set (Field n),MeasurableSet E →
    (∀ d : Field n,vectorNorm d ≤ r*sqrt (n:ℝ) → y+d ∈ E) →
    log ((fieldJacobian j J y)ᵀ*(fieldJacobian j J y)+γ • 1).det ≤
      (n:ℝ)*(j*varianceAverage y^2+ε₁) →
    vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) →
    ENNReal.ofReal (exp (-ε*(n:ℝ))) ≤ localVolume j σ J h E := by
  let η := ε/16
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨ε/4,by positivity,?_⟩
  intro γ hγ
  let noise : ℝ → ℝ := fun σ => (1+η⁻¹)*(6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ
  have hncont : ContinuousAt noise 0 := by dsimp [noise]; fun_prop
  have hnzero : noise 0=0 := by simp [noise]
  obtain ⟨a,ha,hasmall⟩ := nonnegative_continuous_small hncont hnzero (show 0 < ε/4 by positivity)
  refine ⟨min a (r*sqrt γ/2),lt_min ha (by positivity),?_⟩
  intro σ hσ hσ₀
  have hsnoise : noise σ < ε/4 := hasmall σ hσ.le (lt_of_lt_of_le hσ₀ (min_le_left _ _))
  have hsr : 2*σ/sqrt γ ≤ r := by
    apply (div_le_iff₀ (sqrt_pos.mpr hγ)).mpr
    have hh := lt_of_lt_of_le hσ₀ (min_le_right _ _)
    linarith
  let residual : ℝ → ℝ := fun ρ => (1+η⁻¹)*ρ^2/σ^2
  have hrcont : ContinuousAt residual 0 := by dsimp [residual]; fun_prop
  have hrzero : residual 0=0 := by simp [residual]
  obtain ⟨b,hb,hbsmall⟩ := nonnegative_continuous_small hrcont hrzero (show 0 < ε/4 by positivity)
  obtain ⟨N,hN,habsorb⟩ := absorb_three_quarters_exp hε
  refine ⟨b/2,by positivity,N,hN,?_⟩
  intro n hn J hJ h y E hE hball hdet hres
  have hresmall : residual (b/2) < ε/4 := hbsmall _ (by positivity) (by linarith)
  have hloss : (ε/4)/2+2*η+
      (1+η⁻¹)*((b/2)^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ ≤ 3*ε/4 := by
    dsimp [noise] at hsnoise
    dsimp [residual] at hresmall
    dsimp [η] at *
    ring_nf at hsnoise hresmall ⊢
    linarith only [hsnoise,hresmall]
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ENNReal.ofReal ((3/4:ℝ)*exp (-(3*ε/4)*(n:ℝ))) :=
      ENNReal.ofReal_le_ofReal (habsorb n hn)
    _ ≤ ENNReal.ofReal ((3/4:ℝ)*exp (-(n:ℝ)*((ε/4)/2+2*η+
      (1+η⁻¹)*((b/2)^2/σ^2+6*(8*(j+K)^2+128*j^2)*σ^2/γ^2)+4*j*σ/sqrt γ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_left hloss hnn]
    _ ≤ _ := local_volume_quantitative (hN.trans_le hn) hj hK hγ hσ hη (by positivity)
      J hJ h y hE hball hsr hdet hres

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldIntegralMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma measurable_fieldIntegral {n : ℕ} (j t σ : ℝ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) :
    Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)=>
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) {y | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E}) := by
  let H : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p=>ENNReal.ofReal (fieldMollifier j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1))
      (fun i=>t+p.1.2 i) p.2)* E.indicator (fun _=>1) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)
  have hsJ : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1)) :=
    ((goeMatrix_pi_lipschitz (j/(n:ℝ))).continuous.comp (continuous_fst.comp continuous_fst)).add continuous_const
  have htime : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (fun i=>t+p.1.2 i)) := by
    apply continuous_pi
    intro i
    exact continuous_const.add ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1),((fun i=>t+p.1.2 i),p.2))) :=
    hsJ.prodMk (htime.prodMk continuous_snd)
  have hφ := ((continuous_fieldMollifier j σ).comp hmap).measurable.ennreal_ofReal
  have hI : Measurable (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      E.indicator (fun _=>(1 : ℝ≥0∞)) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)) := by
    apply (measurable_const.indicator hE).comp
    unfold goeMatrix
    fun_prop
  have hH : Measurable H := hφ.mul hI
  have he (p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) :
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
        (fun i=>t+p.2 i) {y | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E}=
      ∫⁻ y,H (p,y) := by
    have hs : MeasurableSet {y : Fin n → ℝ | ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E} := hE.preimage (by fun_prop)
    erw [fieldIntegral_indicator _ _ _ _ _ hs]
    apply lintegral_congr
    intro y
    dsimp [H]
    by_cases hy : ((fun q=>goeMatrix (j/(n:ℝ)) p.1 q.1 q.2),y)∈E <;> simp [hy]
  simp_rw [he]
  exact hH.lintegral_prod_right'

lemma measurableSet_badField_section {n : ℕ} (j A ε m : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    MeasurableSet {y : Field n | (W,y)∈badFieldSet n j A ε m} := by
  have hm : Measurable (fun z : Fin n → ℝ=>((fun q : Fin n × Fin n=>W q.1 q.2),z)) :=
    measurable_const.prodMk measurable_id
  have hs := (measurableSet_badFieldFlat n j A ε m).preimage hm
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  rfl

lemma measureReal_union_detector {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E D : Set Ω) (F : Ω → ℝ≥0∞)
    (b p q : ℝ) (hbD : μ.real D ≤ p)
    (hbF : μ.real {x | ENNReal.ofReal b ≤ F x} ≤ q)
    (hdet : ∀ x ∈ E, x∉D → ENNReal.ofReal b ≤ F x) : μ.real E ≤ p+q := by
  apply (measureReal_mono (s₂ := D ∪ {x | ENNReal.ofReal b ≤ F x}) ?_ (measure_ne_top _ _)).trans
  · exact (measureReal_union_le _ _).trans (add_le_add hbD hbF)
  · intro x hx
    by_cases hd : x∈D
    · exact Or.inl hd
    · exact Or.inr (hdet x hx hd)

lemma markov_exponential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F : Ω → ℝ≥0∞} (hF : Measurable F) {a b d : ℝ}
    (hb : ∫⁻ x,F x ∂μ ≤ ENNReal.ofReal (exp (-a*d))) :
    μ.real {x | ENNReal.ofReal (exp (-b*d)) ≤ F x} ≤ exp (-(a-b)*d) := by
  have hm := meas_ge_le_lintegral_div (μ := μ) (ε := ENNReal.ofReal (exp (-b*d))) hF.aemeasurable
    (ENNReal.ofReal_pos.mpr (exp_pos _)).ne' ENNReal.ofReal_ne_top
  have he : ENNReal.ofReal (exp (-a*d))/ENNReal.ofReal (exp (-b*d))=
      ENNReal.ofReal (exp (-(a-b)*d)) := by
    rw [← ENNReal.ofReal_div_of_pos (exp_pos _),← exp_sub]
    congr 2
    ring
  have hx := hm.trans ((ENNReal.div_le_div_right hb _).trans_eq he)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq (ENNReal.toReal_ofReal (exp_pos _).le)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldLogDet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators

lemma spinVariance_difference_norm {n : ℕ} (y d : Field n) :
    vectorNorm (spinVariance (y+d)-spinVariance y) ≤ 2*vectorNorm d := by
  apply vectorNorm_le_of_sq_sum (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (vectorNorm_nonneg _))
  rw [mul_pow,vectorNorm_sq,vectorSqNorm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh : |spinVariance (y+d) i-spinVariance y i| ≤ 2*|d i| := by
    simpa only [spinVariance,magnetization,Pi.add_apply,add_sub_cancel_left] using
      scalar_variance_lipschitz_abs (y i+d i) (y i)
  have ha := mul_self_le_mul_self (abs_nonneg _) hh
  simpa only [sq_abs,← pow_two,mul_pow,Pi.sub_apply] using ha

lemma dot_magnetization_sq_difference {n : ℕ} (y d v : Field n) :
    |((∑ i,magnetization (y+d) i*v i)^2)-(∑ i,magnetization y i*v i)^2| ≤
      2*sqrt (n:ℝ)*vectorNorm d*vectorSqNorm v := by
  let a := ∑ i,magnetization (y+d) i*v i
  let b := ∑ i,magnetization y i*v i
  have ha : |a| ≤ sqrt (n:ℝ)*vectorNorm v :=
    (vector_dot_abs_le (magnetization (y+d)) v).trans
      (mul_le_mul_of_nonneg_right (magnetization_norm_bound (y+d)) (vectorNorm_nonneg _))
  have hb : |b| ≤ sqrt (n:ℝ)*vectorNorm v :=
    (vector_dot_abs_le (magnetization y) v).trans
      (mul_le_mul_of_nonneg_right (magnetization_norm_bound y) (vectorNorm_nonneg _))
  have hab : |a-b| ≤ vectorNorm d*vectorNorm v := by
    have he : a-b=∑ i,(magnetization (y+d)-magnetization y) i*v i := by
      simp only [a,b,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]
    rw [he]
    exact (vector_dot_abs_le _ _).trans
      (mul_le_mul_of_nonneg_right (magnetization_difference_norm y d) (vectorNorm_nonneg _))
  have hsum : |a+b| ≤ 2*sqrt (n:ℝ)*vectorNorm v := (abs_add_le _ _).trans (by linarith)
  change |a^2-b^2| ≤ _
  rw [sq_sub_sq,abs_mul]
  apply (mul_le_mul hsum hab (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sqrt_nonneg _)) (vectorNorm_nonneg _))).trans_eq
  rw [← vectorNorm_sq]
  ring

lemma hessian_field_difference {n : ℕ} (hn : 0 < n) {j A : ℝ} (hj : 0 ≤ j) (_hA : 0 ≤ A)
    (J : Matrix (Fin n) (Fin n) ℝ) (y d a x : Field n)
    (ha0 : ∀ i,0 ≤ a i) (haA : ∀ i,a i ≤ A) :
    |quadraticForm (fieldHessian j J (y+d) a) x-quadraticForm (fieldHessian j J y a) x| ≤
      (6*j*A/sqrt (n:ℝ))*vectorNorm d*vectorSqNorm x := by
  let v : Field n := fun i=>sqrt (a i)*x i
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hs0 : 0 < sqrt (n:ℝ) := sqrt_pos.mpr hn0
  have hv : vectorSqNorm v ≤ A*vectorSqNorm x := by
    unfold vectorSqNorm v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>by
      rw [mul_pow,sq_sqrt (ha0 i)]
      exact mul_le_mul_of_nonneg_right (haA i) (sq_nonneg _))
  have hb : |onsager j (y+d)-onsager j y| ≤ j*(2/sqrt (n:ℝ)*vectorNorm d) := by
    unfold onsager
    rw [← mul_sub,abs_mul,abs_of_nonneg hj]
    exact mul_le_mul_of_nonneg_left (varianceAverage_difference hn y d) hj
  have he : quadraticForm (fieldHessian j J (y+d) a) x-quadraticForm (fieldHessian j J y a) x=
      (onsager j (y+d)-onsager j y)*vectorSqNorm v-
      (2*j/(n:ℝ))*((∑ i,magnetization (y+d) i*v i)^2-(∑ i,magnetization y i*v i)^2) := by
    rw [hessian_quadratic_formula,hessian_quadratic_formula]
    dsimp [v]
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (vectorSqNorm_nonneg v),abs_mul,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hj) hn0.le)]
  have hq := dot_magnetization_sq_difference y d v
  have hfirst := mul_le_mul_of_nonneg_right hb (vectorSqNorm_nonneg v)
  have hsecond := mul_le_mul_of_nonneg_left hq (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hj) hn0.le)
  have hfactor : j*(2/sqrt (n:ℝ)*vectorNorm d)*vectorSqNorm v+
      (2*j/(n:ℝ))*(2*sqrt (n:ℝ)*vectorNorm d*vectorSqNorm v)=
      (6*j/sqrt (n:ℝ))*vectorNorm d*vectorSqNorm v := by
    field_simp
    rw [sq_sqrt hn0.le]
    ring
  apply (add_le_add hfirst hsecond).trans
  rw [hfactor]
  calc
    _ ≤ (6*j/sqrt (n:ℝ))*vectorNorm d*(A*vectorSqNorm x) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg (by positivity) (vectorNorm_nonneg _))
    _ = _ := by ring

lemma badField_neighborhood {n : ℕ} (hn : 0 < n) {j A ε c r : ℝ}
    (hj : 0 ≤ j) (hA : 0 ≤ A) (hε : 0 < ε) (_hr0 : 0 ≤ r)
    (hrε : 2*r ≤ ε/2) (hrc : 6*j*A*r ≤ c/2)
    (W : Matrix (Fin n) (Fin n) ℝ) (y d : Field n)
    (hy : (W,y)∈badFieldSet n j A (ε/2) (c/2))
    (hd : vectorNorm d ≤ r*sqrt (n:ℝ)) :
    (W,y+d)∈badFieldSet n j A ε c := by
  obtain ⟨a,ha,hclose,x,hx,hquad⟩ := hy
  have hs := sqrt_nonneg (n:ℝ)
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnorm : vectorNorm (a-spinVariance y) ≤ (ε/2)*sqrt (n:ℝ) := by
    apply vectorNorm_le_of_sq_sum (by positivity)
    simpa only [Pi.sub_apply,mul_pow,sq_sqrt hn0.le] using hclose
  have hdist : vectorNorm (a-spinVariance (y+d)) ≤ ε*sqrt (n:ℝ) := by
    have he : a-spinVariance (y+d)=(a-spinVariance y)-(spinVariance (y+d)-spinVariance y) := by abel
    rw [he]
    apply (vectorNorm_sub_le _ _).trans
    have hm := (spinVariance_difference_norm y d).trans (mul_le_mul_of_nonneg_left hd (by norm_num))
    nlinarith [mul_le_mul_of_nonneg_right hrε hs]
  refine ⟨a,ha,?_,x,hx,?_⟩
  · have hh := mul_self_le_mul_self (vectorNorm_nonneg (a-spinVariance (y+d))) hdist
    simpa only [← pow_two,vectorNorm_sq,vectorSqNorm,Pi.sub_apply,mul_pow,sq_sqrt hn0.le] using hh
  · have hv : vectorSqNorm x.ofLp=1 := by
      rw [← vectorNorm_sq]
      change ‖WithLp.toLp 2 x.ofLp‖^2=1
      simp only [WithLp.toLp_ofLp,hx,one_pow]
    have hb := hessian_field_difference hn hj hA (plantedInteraction j W) y d a x.ofLp
      (fun i=>(ha i).1) (fun i=>(ha i).2)
    rw [hv,mul_one] at hb
    have hc := (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 6*j*A/sqrt (n:ℝ)))
    have he : (6*j*A/sqrt (n:ℝ))*(r*sqrt (n:ℝ))=6*j*A*r := by field_simp
    rw [he] at hc
    linarith [le_abs_self (quadraticForm (fieldHessian j (plantedInteraction j W) (y+d) a) x.ofLp-
      quadraticForm (fieldHessian j (plantedInteraction j W) y a) x.ofLp)]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_PositiveRootStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem positive_time_root_stability_oai {j A K t₀ T : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hA : 1 ≤ A) (hsub : sqrt j*A < 1) (hK : 0 ≤ K)
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) :
    ∃ ε c ρ a : ℝ,0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ,0 < N ∧
    ∀ (n : ℕ),N ≤ n → ∀ t ∈ Icc t₀ T,
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
      (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
      {p | (∀ z : Field n,vectorNorm (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)*ᵥz) ≤ K*vectorNorm z) ∧
        ∃ y : Field n, vectorNorm (tapField j (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))
          (fun i=>t+p.2 i) y) ≤ ρ*sqrt (n:ℝ) ∧
          (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε c} ≤
        4*exp (-min 1 (1/(π^2*j))*(n:ℝ))+exp (-a*(n:ℝ)) := by
  obtain ⟨m,ε,σb,a,hm,hε,hσb,ha,Nb,hbad⟩ := positive_time_bad_integral hj hj1 hA hsub ht₀ hT
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  let r := min (ε/4) (m/(12*j*A))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : 2*r ≤ ε/2 := by have hh := min_le_left (ε/4) (m/(12*j*A));dsimp [r];linarith
  have hrm : 6*j*A*r ≤ m/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 12*j*A)).mp (min_le_right (ε/4) (m/(12*j*A)))
    dsimp [r]
    nlinarith only [hh]
  obtain ⟨ε₁,hε₁,hvol⟩ := local_volume_uniform hj.le hK hr (half_pos ha)
  obtain ⟨γ,hγ,Nd,hNd,hdet⟩ := field_logdet_uniform hj hj1 hε₁
  obtain ⟨σ₀,hσ₀,hσvol⟩ := hvol γ hγ
  let σ := min (σ₀/2) σb
  have hσ : 0 < σ := lt_min (by positivity) hσb
  have hσless : σ < σ₀ := (min_le_left _ _).trans_lt (by linarith)
  have hσle : σ ≤ σb := min_le_right _ _
  obtain ⟨ρ,hρ,Nv,hNv,hv⟩ := hσvol σ hσ hσless
  refine ⟨ε/2,m/2,ρ,a/2,half_pos hε,half_pos hm,hρ,half_pos ha,
    max Nb (max Nd Nv),hNd.trans_le ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro n hn t ht
  have hnb : Nb ≤ n := (le_max_left _ _).trans hn
  have hnd : Nd ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnv : Nv ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn0 : 0 < n := hNv.trans_le hnv
  let : NeZero n := ⟨Nat.ne_of_gt hn0⟩
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let D : Set (MatrixCoordinates (Fin n) → ℝ) := {g | ∃ y : Field n,
    (n:ℝ)*(j*varianceAverage y^2+ε₁) <
      log ((fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y)ᵀ*
        fieldJacobian j (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) y+γ • 1).det}
  let I : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) → ℝ≥0∞ := fun p=>
    fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)) (fun i=>t+p.2 i)
      {y | (goeMatrix (j/(n:ℝ)) p.1,y)∈badFieldSet n j A ε m}
  have hI : Measurable I := measurable_fieldIntegral j t σ
    (badFieldFlat n j A ε m) (measurableSet_badFieldFlat _ _ _ _ _)
  have hInt : ∫⁻ p,I p ∂μ.prod ν ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
    rw [lintegral_prod _ hI.aemeasurable]
    exact hbad n hnb t ht σ ⟨hσ,hσle⟩
  have hMarkov := markov_exponential (μ.prod ν) hI (b := a/2) hInt
  have hrate : a-a/2=a/2 := by ring
  rw [hrate] at hMarkov
  have hDP : (μ.prod ν).real (D ×ˢ (Set.univ : Set (Fin n → ℝ))) ≤
      4*exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
    rw [measureReal_prod_prod]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one]
    exact hdet n hnd
  apply measureReal_union_detector (μ.prod ν) _ (D ×ˢ Set.univ) I
    (exp (-(a/2)*(n:ℝ))) _ _ hDP hMarkov
  rintro p ⟨hJ,y,hres,hy⟩ hp
  have hp' : p.1∉D := fun hh=>hp ⟨hh,mem_univ _⟩
  dsimp [I]
  rw [fieldIntegral_eq_localVolume hσ]
  apply hv n hnv _ hJ _ y
    {z | (goeMatrix (j/(n:ℝ)) p.1,z)∈badFieldSet n j A ε m}
  · exact measurableSet_badField_section j A ε m _
  · intro d hd
    exact badField_neighborhood hn0 hj.le hA0.le hε hr.le hrε hrm _ y d hy hd
  · exact not_lt.mp (fun hh=>hp' ⟨y,hh⟩)
  · exact hres
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.positive_time_root_stability_oai := @OAI.SKGap.positive_time_root_stability_oai
