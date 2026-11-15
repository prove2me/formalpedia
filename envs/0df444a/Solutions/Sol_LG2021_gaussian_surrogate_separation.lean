-- Prove2me | solution 1 for LG2021.gaussian_surrogate_separation
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T15:09:43.773202+00:00
-- url     : https://prove2.me/submissions/e1c8c31a-e500-41ae-afdf-3b6828c8d4cf

import Mathlib
import Definitions.Def_LG2021_GaussianEstimators
import Definitions.Def_LG2021_GaussianSeparation
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_pi_integration_by_parts
import Theorems.Thm_MeasureTheory_lintegral_sq_mul_measure_ge_le
import Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
import Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_hasGradient

set_option autoImplicit false

/- Translation -/
section


noncomputable section
namespace LG2021.GaussianTranslation
universe uX uY uι
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

private def stdDensity {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

private lemma map_density_comp {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hg]
  change (∫⁻ a, (h ∘ g) a ∂μ.withDensity (f ∘ g)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hg) (hh.comp hg),
    lintegral_withDensity_eq_lintegral_mul _ hf hh]
  exact (lintegral_map (hf.mul hh) hg).symm

private lemma product_density {ι : Type uι} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  have hii (i : ι) : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hn i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) volume :=
    Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hp.restrict (ae_of_all _ (fun x =>
      Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have heq : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      (fun x => ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · simp only [Set.mem_univ_pi] at hx
      rw [Set.indicator_of_mem (show x ∈ univ.pi s by simpa only [Set.mem_univ_pi] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [← integral_indicator (MeasurableSet.univ_pi hs), heq,
    integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun x _ => hn i x) x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))]

private lemma pi_gaussian_density {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      volume.withDensity (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (a i) 1 (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
    gaussianPDF_def]
  exact product_density _ (fun i => integrable_gaussianPDFReal (a i) 1)
    (fun i => gaussianPDFReal_nonneg (a i) 1)

private lemma measurable_stdDensity {ι : Type uι} [Fintype ι] :
    Measurable (stdDensity : EuclideanSpace ℝ ι → ℝ) := by
  unfold stdDensity
  fun_prop

private lemma stdGaussian_density {ι : Type uι} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal (stdDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density (fun _ => 0)]
  have hm := map_density_comp (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (PiLp.volume_preserving_toLp ι).measurable
    (fun x => ENNReal.ofReal (stdDensity x))
    (measurable_stdDensity.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hm
  exact hm

private lemma stdDensity_pos {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    0 < stdDensity x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by norm_num)

private lemma stdDensity_eq {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    stdDensity x = (Real.sqrt (2*Real.pi))⁻¹ ^ (Fintype.card ι) *
      Real.exp (-‖x‖^2/2) := by
  simp only [stdDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simp [EuclideanSpace.norm_sq_eq]

end LG2021.GaussianTranslation

namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussian_eq_withDensity (d : ℕ) :
    gaussian d = volume.withDensity (fun x : Space d => ENNReal.ofReal (gaussianDensity 1 x)) := by
  rw [gaussian, GaussianTranslation.stdGaussian_density]
  congr 1
  funext x
  rw [GaussianTranslation.stdDensity_eq]
  simp [gaussianDensity]

end LG2021

end
end

/- Density -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem gaussianDensity_nonneg {d : ℕ} {s : ℝ} (hs : 0 < s) (x : Space d) :
    0 ≤ gaussianDensity s x := by
  unfold gaussianDensity
  positivity

private theorem gaussianDensity_symmetric_identity {d : ℕ} {s : ℝ} (hs : 0 < s)
    (y mu : Space d) :
    (gaussianDensity s (y - mu) + gaussianDensity s (y + mu)) / 2 =
      Real.exp (-‖mu‖ ^ 2 / (2 * s ^ 2)) * gaussianDensity s y *
        Real.cosh (inner ℝ y mu / s ^ 2) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hminus : -‖y - mu‖ ^ 2 / (2 * s ^ 2) =
      -‖mu‖ ^ 2 / (2 * s ^ 2) + -‖y‖ ^ 2 / (2 * s ^ 2) +
        inner ℝ y mu / s ^ 2 := by
    rw [norm_sub_sq_real]
    ring
  have hplus : -‖y + mu‖ ^ 2 / (2 * s ^ 2) =
      -‖mu‖ ^ 2 / (2 * s ^ 2) + -‖y‖ ^ 2 / (2 * s ^ 2) -
        inner ℝ y mu / s ^ 2 := by
    rw [norm_add_sq_real]
    ring
  simp only [gaussianDensity, hminus, hplus, Real.exp_add, Real.exp_sub, Real.cosh_eq,
    Real.exp_neg]
  ring

/-- Exact symmetric shifted-Gaussian density comparison used in the formalized
curvature argument. -/
private theorem gaussianDensity_symmetric_lower {d : ℕ} {s : ℝ} (hs : 0 < s)
    (y mu : Space d) :
    Real.exp (-‖mu‖ ^ 2 / (2 * s ^ 2)) * gaussianDensity s y ≤
      (gaussianDensity s (y - mu) + gaussianDensity s (y + mu)) / 2 := by
  rw [gaussianDensity_symmetric_identity hs]
  have hnonneg : 0 ≤ Real.exp (-‖mu‖ ^ 2 / (2 * s ^ 2)) * gaussianDensity s y :=
    mul_nonneg (Real.exp_pos _).le (gaussianDensity_nonneg hs y)
  nlinarith [Real.one_le_cosh (inner ℝ y mu / s ^ 2)]

/-- Integrating the symmetric Gaussian comparison against any nonnegative scalar weight.
For a positive semidefinite matrix field, apply this to each of its quadratic forms. -/
private theorem integral_gaussianDensity_symmetric_lower {d : ℕ} {s : ℝ} (hs : 0 < s)
    (mu : Space d) (w : Space d → ℝ) (hw : ∀ x, 0 ≤ w x)
    (h0 : Integrable (fun x => gaussianDensity s x * w x))
    (hm : Integrable (fun x => gaussianDensity s (x - mu) * w x))
    (hp : Integrable (fun x => gaussianDensity s (x + mu) * w x)) :
    Real.exp (-‖mu‖ ^ 2 / (2 * s ^ 2)) * (∫ x, gaussianDensity s x * w x) ≤
      ((∫ x, gaussianDensity s (x - mu) * w x) +
        (∫ x, gaussianDensity s (x + mu) * w x)) / 2 := by
  have hpoint : ∀ x, Real.exp (-‖mu‖ ^ 2 / (2 * s ^ 2)) *
      (gaussianDensity s x * w x) ≤
      (gaussianDensity s (x - mu) * w x + gaussianDensity s (x + mu) * w x) / 2 := by
    intro x
    have hh := mul_le_mul_of_nonneg_right (gaussianDensity_symmetric_lower hs x mu) (hw x)
    nlinarith
  have hh := integral_mono (h0.const_mul _) ((hm.add hp).div_const 2) hpoint
  change (∫ x, Real.exp (-‖mu‖ ^ 2 / (2 * s ^ 2)) * (gaussianDensity s x * w x)) ≤
    ∫ x, (gaussianDensity s (x - mu) * w x +
      gaussianDensity s (x + mu) * w x) / 2 at hh
  simpa only [integral_const_mul, integral_div, integral_add hm hp] using hh

end LG2021

end
end

/- Affine -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private def affineGaussianRatio {d : ℕ} (a : ℝ) (b x : Space d) : ℝ :=
  Real.exp (‖x‖ ^ 2 / 2 - ‖x - b‖ ^ 2 / (2 * a ^ 2)) / a ^ d

private theorem affineGaussianRatio_pos {d : ℕ} {a : ℝ} (ha : 0 < a) (b x : Space d) :
    0 < affineGaussianRatio a b x := by
  unfold affineGaussianRatio
  positivity

private theorem volume_map_affine {d : ℕ} {a : ℝ} (ha : 0 < a) (b : Space d) :
    (volume : Measure (Space d)).map (fun x => a • x + b) =
      ENNReal.ofReal ((a ^ d)⁻¹) • volume := by
  have heq : (fun x : Space d => a • x + b) = (fun y => y + b) ∘ (fun x => a • x) := rfl
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume ha.ne', Measure.map_smul,
    (measurePreserving_add_right volume b).map_eq]
  simp [Space, abs_of_pos (inv_pos.mpr (pow_pos ha _))]

private theorem gaussianDensity_mul_affineRatio {d : ℕ} {a : ℝ} (ha : 0 < a) (b x : Space d) :
    gaussianDensity 1 x * affineGaussianRatio a b x =
      (a ^ d)⁻¹ * gaussianDensity 1 (a⁻¹ • (x - b)) := by
  unfold gaussianDensity affineGaussianRatio
  simp only [mul_one, one_pow, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha)]
  have heq : -(a⁻¹ * ‖x - b‖) ^ 2 / 2 = -‖x - b‖ ^ 2 / (2 * a ^ 2) := by
    field_simp
  rw [heq]
  have he : Real.exp (-‖x‖ ^ 2 / 2) *
      Real.exp (‖x‖ ^ 2 / 2 - ‖x - b‖ ^ 2 / (2 * a ^ 2)) =
      Real.exp (-‖x - b‖ ^ 2 / (2 * a ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ d *
        (Real.exp (-‖x‖ ^ 2 / 2) *
          Real.exp (‖x‖ ^ 2 / 2 - ‖x - b‖ ^ 2 / (2 * a ^ 2))) / a ^ d := by ring
    _ = _ := by rw [he]; ring

/-- Exact affine Gaussian change of measure, including its Jacobian. -/
private theorem gaussian_map_affine {d : ℕ} {a : ℝ} (ha : 0 < a) (b : Space d) :
    (gaussian d).map (fun x => a • x + b) =
      (gaussian d).withDensity (fun x => ENNReal.ofReal (affineGaussianRatio a b x)) := by
  have hρ : Measurable (fun x : Space d => ENNReal.ofReal (gaussianDensity 1 x)) := by
    unfold gaussianDensity
    fun_prop
  have hrat : Measurable (fun x : Space d => ENNReal.ofReal (affineGaussianRatio a b x)) := by
    unfold affineGaussianRatio
    fun_prop
  have hm := GaussianTranslation.map_density_comp (volume : Measure (Space d))
    (fun x => a • x + b) (by fun_prop)
    (fun x => ENNReal.ofReal (gaussianDensity 1 (a⁻¹ • (x - b)))) (by
      unfold gaussianDensity
      fun_prop)
  have hc : (fun x : Space d => ENNReal.ofReal (gaussianDensity 1 (a⁻¹ • (x - b)))) ∘
      (fun x => a • x + b) = fun x => ENNReal.ofReal (gaussianDensity 1 x) := by
    funext x
    simp only [Function.comp_def, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  rw [hc] at hm
  simp only [gaussian_eq_withDensity]
  rw [hm, volume_map_affine ha, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal ((a ^ d)⁻¹)) (by unfold gaussianDensity; fun_prop),
    ← withDensity_mul volume hρ hrat]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ha.le d)),
    ← ENNReal.ofReal_mul (gaussianDensity_nonneg (by norm_num : (0 : ℝ) < 1) x)]
  congr 1
  exact (gaussianDensity_mul_affineRatio ha b x).symm

end LG2021

end
end

/- ChangeOfMeasure -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem integrable_affineGaussianRatio_iff {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    Integrable (fun x => affineGaussianRatio a b x * F x) (gaussian d) ↔
      Integrable (fun u => F (a • u + b)) (gaussian d) := by
  have hrat : Measurable (fun x : Space d => ENNReal.ofReal (affineGaussianRatio a b x)) := by
    unfold affineGaussianRatio
    fun_prop
  have hw := integrable_withDensity_iff_integrable_smul' (μ := gaussian d) hrat
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (g := F)
  simp only [ENNReal.toReal_ofReal (affineGaussianRatio_pos ha b _).le, smul_eq_mul] at hw
  have hm := integrable_map_measure (μ := gaussian d)
    (f := fun x : Space d => a • x + b) hF.aestronglyMeasurable (by fun_prop)
  rw [gaussian_map_affine ha b] at hm
  exact hw.symm.trans hm

private theorem integral_affineGaussianRatio {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    (∫ x, affineGaussianRatio a b x * F x ∂gaussian d) =
      ∫ u, F (a • u + b) ∂gaussian d := by
  have hrat : Measurable (fun x : Space d => ENNReal.ofReal (affineGaussianRatio a b x)) := by
    unfold affineGaussianRatio
    fun_prop
  calc
    _ = ∫ x, F x ∂(gaussian d).withDensity (fun x => ENNReal.ofReal (affineGaussianRatio a b x)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hrat
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (affineGaussianRatio_pos ha b _).le, smul_eq_mul]
    _ = ∫ x, F x ∂(gaussian d).map (fun x => a • x + b) := by rw [gaussian_map_affine ha b]
    _ = _ := integral_map (by fun_prop) hF.aestronglyMeasurable

private theorem integrable_likelihoodRatio_iff {d : ℕ} {lambda : ℝ} (hl : lambda < 1)
    (z : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    Integrable (fun x => Concentration.likelihoodRatio lambda z x * F x) (gaussian d) ↔
      Integrable (fun u => F ((1 - lambda) • u + lambda • z)) (gaussian d) := by
  exact integrable_affineGaussianRatio_iff (sub_pos.mpr hl) (lambda • z) hF

private theorem integral_likelihoodRatio {d : ℕ} {lambda : ℝ} (hl : lambda < 1)
    (z : Space d) {F : Space d → ℝ} (hF : Measurable F) :
    (∫ x, Concentration.likelihoodRatio lambda z x * F x ∂gaussian d) =
      ∫ u, F ((1 - lambda) • u + lambda • z) ∂gaussian d := by
  exact integral_affineGaussianRatio (sub_pos.mpr hl) (lambda • z) hF

end LG2021

end
end

/- Stein -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- The finite product of scalar standard normals gives the concrete Euclidean Gaussian. -/
private theorem gaussian_toLp_measurePreserving (d : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → Space d)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) (gaussian d) := by
  refine ⟨by fun_prop, ?_⟩
  exact map_pi_eq_stdGaussian

/-- Coordinatewise Stein identity for the actual Euclidean Gaussian, under absolute
integrability assumptions. -/
private theorem gaussian_coordinate_integration_by_parts {d : ℕ} (i : Fin d)
    {f : Space d → ℝ} {D : Space d → Space d →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt f (D x) x)
    (hf : Integrable f (gaussian d))
    (hdf : Integrable (fun x => D x (EuclideanSpace.basisFun (Fin d) ℝ i)) (gaussian d))
    (hxf : Integrable (fun x => x i * f x) (gaussian d)) :
    (∫ x, D x (EuclideanSpace.basisFun (Fin d) ℝ i) ∂gaussian d) =
      ∫ x, x i * f x ∂gaussian d := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e : (Fin (n + 1) → ℝ) ≃L[ℝ] Space (n + 1) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm
    have hp : MeasurePreserving e
        (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) (gaussian (n + 1)) :=
      gaussian_toLp_measurePreserving (n + 1)
    have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    rw [← hp.integral_comp hemb (fun x => D x (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)),
      ← hp.integral_comp hemb (fun x => x i * f x)]
    apply HighDimProb.RandomProcesses.gaussian_pi_integration_by_parts i
      (f := fun x => f (e x))
      (df := fun x => D (e x) (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i))
      _ (hp.integrable_comp_of_integrable hf) (hp.integrable_comp_of_integrable hdf)
      (hp.integrable_comp_of_integrable hxf)
    intro x t
    have ht := e.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)
    have h := (hD (e (Function.update x i t))).comp_hasDerivAt t ht
    have he1 : e (Pi.single i (1 : ℝ)) = EuclideanSpace.basisFun (Fin (n + 1)) ℝ i := by
      ext j
      simp [e, EuclideanSpace.basisFun_apply, PiLp.single_apply]
    change HasDerivAt (fun y => f (e (Function.update x i y)))
      (D (e (Function.update x i t)) (e (Pi.single i (1 : ℝ)))) t at h
    rw [he1] at h
    exact h

end LG2021

end
end

/- SteinBounded -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem gaussian_integrable_bounded {d : ℕ} {f : Space d → ℝ}
    (hf : AEStronglyMeasurable f (gaussian d)) {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Integrable f (gaussian d) :=
  Integrable.mono' (integrable_const B) hf (Filter.Eventually.of_forall hB)

/-- Bounded smooth tests satisfy the coordinate Stein identity without separate integrability
premises. -/
private theorem gaussian_coordinate_integration_by_parts_bounded {d : ℕ} (i : Fin d)
    {f : Space d → ℝ} {D : Space d → Space d →L[ℝ] ℝ}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C) :
    (∫ x, D x (EuclideanSpace.basisFun (Fin d) ℝ i) ∂gaussian d) =
      ∫ x, x i * f x ∂gaussian d := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have he : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  apply gaussian_coordinate_integration_by_parts i hD
  · exact gaussian_integrable_bounded hf.aestronglyMeasurable hB
  · apply gaussian_integrable_bounded (by fun_prop) (B := C)
    intro x
    exact ((D x).le_opNorm (e i)).trans (by simpa only [he, mul_one] using hC x)
  · apply Integrable.mono' ((IsGaussian.integrable_fun_id (μ := gaussian d)).norm.const_mul B)
      (by fun_prop)
    filter_upwards with x
    rw [norm_mul]
    have hxi : ‖x i‖ ≤ ‖x‖ := by
      have h := norm_inner_le_norm (𝕜 := ℝ) (e i) x
      rw [he, one_mul] at h
      simpa only [e, EuclideanSpace.basisFun_inner] using h
    calc
      ‖x i‖ * ‖f x‖ ≤ ‖x‖ * B := mul_le_mul hxi (hB x) (norm_nonneg _) (norm_nonneg _)
      _ = B * ‖x‖ := mul_comm _ _

end LG2021

end
end

/- Comparison -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem affineGaussianRatio_symmetric_identity {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b x : Space d) :
    (affineGaussianRatio a b x + affineGaussianRatio a (-b) x) / 2 =
      Real.exp (-‖b‖^2/(2*a^2)) * affineGaussianRatio a 0 x *
        Real.cosh (inner ℝ x b / a^2) := by
  have hm : ‖x‖^2/2 - ‖x-b‖^2/(2*a^2) =
      -‖b‖^2/(2*a^2) + (‖x‖^2/2-‖x‖^2/(2*a^2)) + inner ℝ x b / a^2 := by
    rw [norm_sub_sq_real]
    ring
  have hp : ‖x‖^2/2 - ‖x+b‖^2/(2*a^2) =
      -‖b‖^2/(2*a^2) + (‖x‖^2/2-‖x‖^2/(2*a^2)) - inner ℝ x b / a^2 := by
    rw [norm_add_sq_real]
    ring
  simp only [affineGaussianRatio, sub_neg_eq_add, sub_zero, hm, hp,
    Real.exp_add, Real.exp_sub, Real.cosh_eq, Real.exp_neg]
  ring

private theorem affineGaussianRatio_symmetric_lower {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b x : Space d) :
    Real.exp (-‖b‖^2/(2*a^2)) * affineGaussianRatio a 0 x ≤
      (affineGaussianRatio a b x + affineGaussianRatio a (-b) x)/2 := by
  rw [affineGaussianRatio_symmetric_identity ha]
  have hp := affineGaussianRatio_pos ha (0 : Space d) x
  have he := Real.exp_pos (-‖b‖^2/(2*a^2))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.one_le_cosh (inner ℝ x b / a^2)) (mul_nonneg he.le hp.le)

private theorem integrable_bounded_affineGaussianRatio {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d) {F : Space d → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) :
    Integrable (fun x => affineGaussianRatio a b x * F x) (gaussian d) := by
  apply (integrable_affineGaussianRatio_iff ha b hF).2
  exact gaussian_integrable_bounded (hF.comp (by fun_prop)).aestronglyMeasurable (fun x => hC _)

private theorem gaussian_affine_symmetric_lower {d : ℕ} {a : ℝ} (ha : 0 < a)
    (b : Space d) {F : Space d → ℝ} (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    Real.exp (-‖b‖^2/(2*a^2)) * (∫ x, F (a • x) ∂gaussian d) ≤
      ((∫ x, F (a • x+b) ∂gaussian d) + (∫ x, F (a • x-b) ∂gaussian d))/2 := by
  have hi0 := integrable_bounded_affineGaussianRatio ha (0 : Space d) hF hC
  have hip := integrable_bounded_affineGaussianRatio ha b hF hC
  have him := integrable_bounded_affineGaussianRatio ha (-b) hF hC
  have h := integral_mono (hi0.const_mul (Real.exp (-‖b‖^2/(2*a^2))))
    ((hip.add him).div_const 2) (fun x => ?_)
  · simp only [Pi.add_apply] at h
    simp only [integral_const_mul, integral_div, integral_add hip him,
      integral_affineGaussianRatio ha _ hF, add_zero, ← sub_eq_add_neg] at h
    exact h
  · have hh := mul_le_mul_of_nonneg_right (affineGaussianRatio_symmetric_lower ha b x) (hF0 x)
    simp only [Pi.add_apply]
    nlinarith

private theorem affineGaussianRatio_scale_lower {d : ℕ} {a B c : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hc : (1-a^2)*B^2/(2*a^2) ≤ c) {x : Space d} (hx : ‖x‖ ≤ B) :
    Real.exp (-c) ≤ affineGaussianRatio a 0 x := by
  have ha2 : 0 < 2*a^2 := by positivity
  have ha21 : a^2 ≤ 1 := by nlinarith
  have hnorm : ‖x‖^2 ≤ B^2 := by nlinarith [norm_nonneg x]
  have hex : -c ≤ ‖x‖^2/2 - ‖x‖^2/(2*a^2) := by
    have hh := mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr ha21)
    have hle : (1-a^2)*‖x‖^2/(2*a^2) ≤ c :=
      (div_le_div_of_nonneg_right hh ha2.le).trans hc
    have heq : ‖x‖^2/2 - ‖x‖^2/(2*a^2) = -((1-a^2)*‖x‖^2/(2*a^2)) := by
      field_simp
      <;> ring
    rw [heq]
    exact neg_le_neg hle
  have hpow : a^d ≤ 1 := pow_le_one₀ ha.le ha1
  have hp : 0 < a^d := pow_pos ha d
  unfold affineGaussianRatio
  rw [sub_zero]
  calc
    _ ≤ Real.exp (‖x‖^2/2-‖x‖^2/(2*a^2)) := Real.exp_le_exp.mpr hex
    _ ≤ _ := (le_div_iff₀ hp).2
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le)

private theorem gaussian_scale_truncated_lower {d : ℕ} {a B c : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hc : (1-a^2)*B^2/(2*a^2) ≤ c)
    {F : Space d → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    Real.exp (-c) * (∫ x in {x : Space d | ‖x‖ ≤ B}, F x ∂gaussian d) ≤
      ∫ x, F (a • x) ∂gaussian d := by
  have hset : MeasurableSet {x : Space d | ‖x‖ ≤ B} := measurableSet_le measurable_norm measurable_const
  have hi := gaussian_integrable_bounded hF.aestronglyMeasurable hC
  have hw := integrable_bounded_affineGaussianRatio ha (0 : Space d) hF hC
  have h := integral_mono ((hi.indicator hset).const_mul (Real.exp (-c))) hw (fun x => ?_)
  · rw [integral_const_mul, integral_indicator hset, integral_affineGaussianRatio ha _ hF] at h
    simpa only [add_zero] using h
  · by_cases hx : ‖x‖ ≤ B
    · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hx]
      exact mul_le_mul_of_nonneg_right (affineGaussianRatio_scale_lower ha ha1 hB hc hx) (hF0 x)
    · simp only [Set.indicator, Set.mem_setOf_eq, if_neg hx, mul_zero]
      exact mul_nonneg (affineGaussianRatio_pos ha 0 x).le (hF0 x)

private theorem gaussian_affine_symmetric_truncated_lower {d : ℕ} {a B c t : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hc : (1-a^2)*B^2/(2*a^2) ≤ c) (b : Space d)
    (ht : ‖b‖^2/(2*a^2) ≤ t)
    {F : Space d → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    Real.exp (-(c+t)) * (∫ x in {x : Space d | ‖x‖ ≤ B}, F x ∂gaussian d) ≤
      ((∫ x, F (a • x+b) ∂gaussian d)+(∫ x, F (a • x-b) ∂gaussian d))/2 := by
  have hscale := gaussian_scale_truncated_lower ha ha1 hB hc hF hF0 hC
  have hpos : 0 ≤ ∫ x, F (a • x) ∂gaussian d := integral_nonneg (fun x => hF0 _)
  have hexp : Real.exp (-t) ≤ Real.exp (-‖b‖^2/(2*a^2)) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg ht
  calc
    _ = Real.exp (-t) * (Real.exp (-c) *
        ∫ x in {x : Space d | ‖x‖ ≤ B}, F x ∂gaussian d) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-t) * (∫ x, F (a • x) ∂gaussian d) :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le
    _ ≤ Real.exp (-‖b‖^2/(2*a^2)) * (∫ x, F (a • x) ∂gaussian d) :=
      mul_le_mul_of_nonneg_right hexp hpos
    _ ≤ _ := gaussian_affine_symmetric_lower ha b hF hF0 hC

end LG2021

end
end

/- Hessian -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private def partialDerivative {d : ℕ} (f : Space d → ℝ) (i : Fin d) (x : Space d) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin d) ℝ i)

private def secondPartialDerivative {d : ℕ} (f : Space d → ℝ) (i j : Fin d) (x : Space d) : ℝ :=
  partialDerivative (partialDerivative f i) j x

/-- The second-order Gaussian identity uses the centered Hermite score.
Its absolute-integrability hypotheses are explicit. -/
private theorem gaussian_second_partial_identity {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (i j : Fin d)
    (hf : Integrable f (gaussian d))
    (hfi : Integrable (partialDerivative f i) (gaussian d))
    (hxj : Integrable (fun x => x j * f x) (gaussian d))
    (hxjfi : Integrable (fun x => x j * partialDerivative f i x) (gaussian d))
    (hxixjf : Integrable (fun x => x i * (x j * f x)) (gaussian d))
    (hsecond : Integrable (secondPartialDerivative f i j) (gaussian d)) :
    (∫ x, secondPartialDerivative f i j x ∂gaussian d) = curvatureMatrix f i j := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hdiff : Differentiable ℝ f := hs.differentiable (by norm_num)
  have hp : ContDiff ℝ 1 (partialDerivative f i) := by
    exact (hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hfirst := gaussian_coordinate_integration_by_parts j
    (fun x => (hp.differentiable (by norm_num) x).hasFDerivAt) hfi hsecond hxjfi
  change (∫ x, secondPartialDerivative f i j x ∂gaussian d) =
    ∫ x, x j * partialDerivative f i x ∂gaussian d at hfirst
  let P : Space d → Space d →L[ℝ] ℝ := fun x =>
    x j • fderiv ℝ f x + f x • innerSL ℝ (e j)
  have hP : ∀ x, HasFDerivAt (fun y : Space d => y j * f y) (P x) x := by
    intro x
    have hcoord : HasFDerivAt (fun y : Space d => y j) (innerSL ℝ (e j)) x := by
      have h := (innerSL ℝ (e j)).hasFDerivAt (x := x)
      change HasFDerivAt (fun y => inner ℝ (e j) y) (innerSL ℝ (e j)) x at h
      simpa only [e, EuclideanSpace.basisFun_inner] using h
    have h := hcoord.mul (hdiff x).hasFDerivAt
    change HasFDerivAt (fun y : Space d => y j * f y)
      (x j • fderiv ℝ f x + f x • innerSL ℝ (e j)) x at h
    exact h
  have hP_apply (x : Space d) : P x (e i) =
      x j * partialDerivative f i x + (if i = j then 1 else 0) * f x := by
    simp only [P, add_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, partialDerivative]
    have hei : inner ℝ (e j) (e i) = if i = j then 1 else 0 := by
      simpa only [eq_comm] using orthonormal_iff_ite.mp e.orthonormal j i
    rw [hei]
    ring
  have hPi : Integrable (fun x => P x (e i)) (gaussian d) := by
    simp_rw [hP_apply]
    exact hxjfi.add (hf.const_mul _)
  have hprod := gaussian_coordinate_integration_by_parts i hP hxj hPi hxixjf
  change (∫ x, P x (e i) ∂gaussian d) =
    ∫ x, x i * (x j * f x) ∂gaussian d at hprod
  simp_rw [hP_apply] at hprod
  rw [integral_add hxjfi (hf.const_mul _), integral_const_mul] at hprod
  rw [hfirst]
  unfold curvatureMatrix
  have heq : (fun x : Space d => (x i * x j - if i = j then 1 else 0) * f x) =
      (fun x => x i * (x j * f x) - (if i = j then 1 else 0) * f x) := by
    funext x
    ring
  rw [heq, integral_sub hxixjf (hf.const_mul _), integral_const_mul]
  linarith

end LG2021

end
end

/- Surrogate -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem integrable_lipschitz_gaussian_affine {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (a : ℝ) (z : Space d) :
    Integrable (fun x => f (a • x + z)) (gaussian d) := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have hmajor : Integrable (fun x : Space d => ‖f 0‖ +
      (K : ℝ) * (|a| * ‖x‖ + ‖z‖)) (gaussian d) :=
    (integrable_const _).add (((hx.norm.const_mul |a|).add (integrable_const _)).const_mul _)
  apply hmajor.mono' (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  calc
    ‖f (a • x + z)‖ ≤ ‖f 0‖ + ‖f 0 - f (a • x + z)‖ := norm_le_insert _ _
    _ ≤ ‖f 0‖ + (K : ℝ) * ‖a • x + z‖ := by
      gcongr
      simpa only [zero_sub, norm_neg] using hf.norm_sub_le 0 (a • x + z)
    _ ≤ ‖f 0‖ + (K : ℝ) * (|a| * ‖x‖ + ‖z‖) := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • x) z

private theorem integrable_lipschitz_gaussian {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : Integrable f (gaussian d) := by
  simpa using integrable_lipschitz_gaussian_affine hf 1 0

private theorem gaussianMean_ge_value_zero {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) : f 0 ≤ gaussianMean f := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have h := hc.map_integral_le hf.continuous.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hx (integrable_lipschitz_gaussian hf)
  simpa [gaussianMean, gaussian] using h

private theorem surrogate_le {d : ℕ} {f : Space d → ℝ} {K : NNReal} {lambda : ℝ}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hl : 0 < lambda) (hl1 : lambda ≤ 1) (z : Space d) : surrogate lambda f z ≤ f z := by
  have hi := integrable_lipschitz_gaussian hf
  have hia := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • z)
  have hp : ∀ x : Space d, f ((1 - lambda) • x + lambda • z) ≤
      (1 - lambda) * f x + lambda * f z := by
    intro x
    simpa only [smul_eq_mul] using hc.2 (Set.mem_univ x) (Set.mem_univ z)
      (sub_nonneg.mpr hl1) hl.le (by ring : 1 - lambda + lambda = 1)
  have hh := integral_mono hia ((hi.const_mul _).add (integrable_const _)) hp
  change (∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d) ≤
    ∫ x, (1 - lambda) * f x + lambda * f z ∂gaussian d at hh
  simp only [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul] at hh
  change gaussianMean f + (_ - gaussianMean f) / lambda ≤ f z
  have hd : ((∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d) -
      gaussianMean f) / lambda ≤ f z - gaussianMean f := by
    apply (div_le_iff₀ hl).2
    unfold gaussianMean
    nlinarith
  linarith

private theorem surrogate_convex {d : ℕ} {f : Space d → ℝ} {K : NNReal} {lambda : ℝ}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (hl : 0 < lambda) :
    ConvexOn ℝ Set.univ (surrogate lambda f) := by
  let F : Space d → ℝ := fun z => ∫ x, f ((1 - lambda) • x + lambda • z) ∂gaussian d
  have hF : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, ?_⟩
    intro z hz w hw a b ha hb hab
    have hiz := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • z)
    have hiw := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • w)
    have him := integrable_lipschitz_gaussian_affine hf (1 - lambda)
      (lambda • (a • z + b • w))
    have hpoint : ∀ x : Space d,
        f ((1 - lambda) • x + lambda • (a • z + b • w)) ≤
          a * f ((1 - lambda) • x + lambda • z) +
          b * f ((1 - lambda) • x + lambda • w) := by
      intro x
      have heq : a • ((1 - lambda) • x + lambda • z) +
          b • ((1 - lambda) • x + lambda • w) =
          (1 - lambda) • x + lambda • (a • z + b • w) := by
        calc
          _ = (a + b) • ((1 - lambda) • x) + lambda • (a • z + b • w) := by module
          _ = _ := by rw [hab, one_smul]
      simpa only [heq, smul_eq_mul] using hc.2
        (Set.mem_univ ((1 - lambda) • x + lambda • z))
        (Set.mem_univ ((1 - lambda) • x + lambda • w)) ha hb hab
    have hh := integral_mono him ((hiz.const_mul a).add (hiw.const_mul b)) hpoint
    change (∫ x, f ((1 - lambda) • x + lambda • (a • z + b • w)) ∂gaussian d) ≤
      ∫ x, a * f ((1 - lambda) • x + lambda • z) +
        b * f ((1 - lambda) • x + lambda • w) ∂gaussian d at hh
    simpa only [F, integral_add (hiz.const_mul a) (hiw.const_mul b), integral_const_mul,
      smul_eq_mul] using hh
  have hscaled := (hF.smul (show 0 ≤ 1 / lambda by positivity)).add_const
    (gaussianMean f - gaussianMean f / lambda)
  have heq : surrogate lambda f = fun z => (1 / lambda) * F z +
      (gaussianMean f - gaussianMean f / lambda) := by
    funext z
    simp only [surrogate, F]
    ring
  rw [heq]
  exact hscaled

/-- Gaussian averaging and the factor `1 / lambda` preserve the original Lipschitz constant. -/
private theorem surrogate_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal} {lambda : ℝ}
    (hf : LipschitzWith K f) (hl : 0 < lambda) : LipschitzWith K (surrogate lambda f) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro z w
  have hiz := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • z)
  have hiw := integrable_lipschitz_gaussian_affine hf (1 - lambda) (lambda • w)
  have heq : surrogate lambda f z - surrogate lambda f w =
      (∫ x : Space d, f ((1 - lambda) • x + lambda • z) -
        f ((1 - lambda) • x + lambda • w) ∂gaussian d) / lambda := by
    rw [integral_sub hiz hiw]
    unfold surrogate
    ring
  rw [heq, norm_div, show ‖lambda‖ = lambda from Real.norm_of_nonneg hl.le]
  apply (div_le_iff₀ hl).2
  have hb : ∀ᵐ x : Space d ∂gaussian d,
      ‖f ((1 - lambda) • x + lambda • z) - f ((1 - lambda) • x + lambda • w)‖ ≤
        (K : ℝ) * ‖z - w‖ * lambda := by
    filter_upwards with x
    have h := hf.norm_sub_le ((1 - lambda) • x + lambda • z)
      ((1 - lambda) • x + lambda • w)
    simpa only [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hl, mul_left_comm, mul_comm, mul_assoc] using h
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

end LG2021

end
end

/- Integrability -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem integrable_gaussian_norm_pow (d k : ℕ) :
    Integrable (fun x : Space d => ‖x‖ ^ k) (gaussian d) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (gaussian d) (k : ENNReal) (by simp)).integrable_norm_pow'

private theorem integrable_gaussian_norm_pow_mul_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (k : ℕ) :
    Integrable (fun x : Space d => ‖x‖ ^ k * f x) (gaussian d) := by
  have hmajor : Integrable (fun x : Space d => ‖f 0‖ * ‖x‖ ^ k +
      (K : ℝ) * ‖x‖ ^ (k + 1)) (gaussian d) :=
    ((integrable_gaussian_norm_pow d k).const_mul _).add
      ((integrable_gaussian_norm_pow d (k + 1)).const_mul _)
  apply hmajor.mono' (((continuous_norm.pow k).mul hf.continuous).aestronglyMeasurable)
  filter_upwards with x
  have hfg : ‖f x‖ ≤ ‖f 0‖ + (K : ℝ) * ‖x‖ := by
    calc
      _ ≤ ‖f 0‖ + ‖f 0 - f x‖ := norm_le_insert _ _
      _ ≤ _ := by
        gcongr
        simpa only [zero_sub, norm_neg] using hf.norm_sub_le 0 x
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) k)]
  calc
    ‖x‖ ^ k * ‖f x‖ ≤ ‖x‖ ^ k * (‖f 0‖ + (K : ℝ) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hfg (pow_nonneg (norm_nonneg x) k)
    _ = _ := by rw [pow_succ]; ring

private theorem integrable_gaussian_coordinate_mul_lipschitz {d : ℕ} {f : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (i : Fin d) :
    Integrable (fun x : Space d => x i * f x) (gaussian d) := by
  apply (integrable_gaussian_norm_pow_mul_lipschitz hf 1).norm.mono'
    (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).mul hf.continuous).aestronglyMeasurable)
  filter_upwards with x
  simp only [Pi.mul_apply, norm_mul, pow_one, norm_norm]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg (f x))

private theorem integrable_gaussian_two_coordinates_mul_lipschitz {d : ℕ} {f : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (i j : Fin d) :
    Integrable (fun x : Space d => x i * (x j * f x)) (gaussian d) := by
  apply (integrable_gaussian_norm_pow_mul_lipschitz hf 2).norm.mono'
    (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).mul ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).mul hf.continuous)).aestronglyMeasurable)
  filter_upwards with x
  simp only [Pi.mul_apply, norm_mul, norm_pow, norm_norm]
  calc
    ‖x i‖ * (‖x j‖ * ‖f x‖) ≤ ‖x‖ * (‖x‖ * ‖f x‖) := by
      gcongr
      · exact PiLp.norm_apply_le x i
      · exact PiLp.norm_apply_le x j
    _ = _ := by ring

end LG2021

end
end

/- Convex -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- The differential of a differentiable convex function is a supporting functional. -/
private theorem convex_supporting_fderiv {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) {x : Space d} {D : Space d →L[ℝ] ℝ}
    (hD : HasFDerivAt f D x) (y : Space d) : f x + D (y - x) ≤ f y := by
  let line : ℝ → Space d := fun t => x + t • (y - x)
  have hline : HasDerivAt line (y - x) 0 := by
    simpa [line] using (hasDerivAt_id (0 : ℝ)).smul_const (y - x) |>.const_add x
  have hder : HasDerivAt (fun t => f (line t)) (D (y - x)) 0 := by
    have hDx : HasFDerivAt f D (line 0) := by simpa [line] using hD
    exact hDx.comp_hasDerivAt 0 hline
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => f (line t)) := by
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb s t hs ht hst
    have heq : s • line a + t • line b = line (s * a + t * b) := by
      dsimp [line]
      calc
        _ = (s + t) • x + (s * a + t * b) • (y - x) := by module
        _ = _ := by rw [hst, one_smul]
    simpa only [smul_eq_mul, heq] using hc.2 (Set.mem_univ (line a))
      (Set.mem_univ (line b)) hs ht hst
  have h := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hder
  simp [slope_def_field, line] at h
  simp only [map_sub]
  linarith

/-- Subtracting the affine support at the origin gives a nonnegative function. -/
private theorem convex_remainder_nonneg {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) {D : Space d →L[ℝ] ℝ}
    (hD : HasFDerivAt f D 0) (x : Space d) : 0 ≤ f x - f 0 - D x := by
  have h := convex_supporting_fderiv hc hD x
  simp only [sub_zero] at h
  linarith

/-- The pointwise radial inequality used before Gaussian integration by parts. -/
private theorem convex_radial_derivative_lower {d : ℕ} {h : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ h) (hzero : h 0 = 0) {x : Space d}
    {D : Space d →L[ℝ] ℝ} (hD : HasFDerivAt h D x) : h x ≤ D x := by
  have h := convex_supporting_fderiv hc hD 0
  simpa only [zero_sub, map_neg, hzero, add_neg_le_iff_le_add, zero_add] using h

end LG2021

end
end

/- PositiveHessian -/
section

noncomputable section
namespace LG2021

/-- Restricting a convex Euclidean function to an affine line preserves convexity. -/
private theorem convexOn_affine_line {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (x v : Space d) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb s t hs ht hst
  have heq : s • (x + a • v) + t • (x + b • v) = x + (s * a + t * b) • v := by
    calc
      _ = (s + t) • x + (s * a + t * b) • v := by module
      _ = _ := by rw [hst, one_smul]
  simpa only [smul_eq_mul, heq] using hc.2 (Set.mem_univ (x + a • v))
    (Set.mem_univ (x + b • v)) hs ht hst

/-- A twice continuously differentiable convex function has nonnegative curvature in every
actual Euclidean direction. -/
private theorem convex_second_fderiv_nonneg {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f) (x v : Space d) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hdf := hs.differentiable (by norm_num)
  have hD := (hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφ (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • v))
      (fderiv ℝ f (x + t • v) v) t :=
    (hdf (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have hmono : Monotone (fun t : ℝ => fderiv ℝ f (x + t • v) v) := by
    have hm := (convexOn_affine_line hc x v).monotoneOn_deriv
      (fun t _ => (hφ t).differentiableAt)
    intro a b hab
    have h := hm (Set.mem_univ a) (Set.mem_univ b) hab
    simpa only [(hφ a).deriv, (hφ b).deriv] using h
  have hDline : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v))
      (fderiv ℝ (fderiv ℝ f) x v) 0 := by
    have h := (hD (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 (hline 0)
    simpa only [zero_smul, add_zero, Function.comp_def] using h
  have hψ : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt 0 hDline
  exact hψ.nonneg_of_monotone hmono

end LG2021

end
end

/- HessianAnalysis -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private def laplacian {d : ℕ} (f : Space d → ℝ) (x : Space d) : ℝ :=
  ∑ i, secondPartialDerivative f i i x

private theorem partialDerivative_hasFDerivAt {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (i : Fin d) (x : Space d) :
    HasFDerivAt (partialDerivative f i)
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)).comp
        (fderiv ℝ (fderiv ℝ f) x)) x := by
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)).hasFDerivAt.comp x
    (((hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt)

private theorem secondPartialDerivative_eq {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (i j : Fin d) (x : Space d) :
    secondPartialDerivative f i j x = fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  change (fderiv ℝ (partialDerivative f i) x) (EuclideanSpace.basisFun (Fin d) ℝ j) = _
  rw [(partialDerivative_hasFDerivAt hs i x).fderiv]
  rfl

private theorem norm_partialDerivative_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (i : Fin d) (x : Space d) :
    ‖partialDerivative f i x‖ ≤ (K : ℝ) := by
  have he := (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one i
  exact ((fderiv ℝ f x).le_opNorm _).trans (by
    simpa only [he, mul_one] using norm_fderiv_le_of_lipschitz ℝ hf)

private theorem partialDerivative_lipschitz {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hg : LipschitzWith J (fderiv ℝ f)) (i : Fin d) :
    LipschitzWith J (partialDerivative f i) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  change ‖(fderiv ℝ f x - fderiv ℝ f y) (EuclideanSpace.basisFun (Fin d) ℝ i)‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ f x - fderiv ℝ f y‖ * ‖EuclideanSpace.basisFun (Fin d) ℝ i‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
      rw [(EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.norm_eq_one i, mul_one]
      exact hg.norm_sub_le x y

private theorem gaussian_second_partial_identity_lipschitz {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) (i j : Fin d) :
    (∫ x, secondPartialDerivative f i j x ∂gaussian d) = curvatureMatrix f i j := by
  have hp := partialDerivative_lipschitz hg i
  apply gaussian_second_partial_identity hs i j
    (integrable_lipschitz_gaussian hf) (integrable_lipschitz_gaussian hp)
    (integrable_gaussian_coordinate_mul_lipschitz hf j)
    (integrable_gaussian_coordinate_mul_lipschitz hp j)
    (integrable_gaussian_two_coordinates_mul_lipschitz hf i j)
  apply gaussian_integrable_bounded
    (((hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      (by norm_num) |>.clm_apply continuous_const |>.aestronglyMeasurable)
    (B := (J : ℝ))
  intro x
  exact norm_partialDerivative_le hp j x

private theorem laplacian_continuous {d : ℕ} {f : Space d → ℝ} (hs : ContDiff ℝ 2 f) :
    Continuous (laplacian f) := by
  apply continuous_finset_sum
  intro i hi
  exact (((hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      (by norm_num)).clm_apply continuous_const

private theorem norm_laplacian_le {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hg : LipschitzWith J (fderiv ℝ f)) (x : Space d) :
    ‖laplacian f x‖ ≤ (d : ℝ) * J := by
  calc
    _ ≤ ∑ i : Fin d, ‖secondPartialDerivative f i i x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (J : ℝ) := Finset.sum_le_sum (fun i _ =>
      norm_partialDerivative_le (partialDerivative_lipschitz hg i) i x)
    _ = _ := by simp

private theorem laplacian_nonneg {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f) (x : Space d) :
    0 ≤ laplacian f x := by
  apply Finset.sum_nonneg
  intro i hi
  rw [secondPartialDerivative_eq hs]
  exact convex_second_fderiv_nonneg hc hs x _

private theorem fderiv_radial_eq_sum {d : ℕ} (f : Space d → ℝ) (x : Space d) :
    fderiv ℝ f x x = ∑ i, x i * partialDerivative f i x := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  calc
    _ = fderiv ℝ f x (∑ i, x i • e i) := by
      congr 1
      exact (e.sum_repr x).symm
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, e, partialDerivative]

end LG2021

end
end

/- Comparator -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- The comparator gap is nonnegative for a convex loss and a ball containing zero. -/
private theorem gaussianGap_nonneg {d : ℕ} {f : Space d → ℝ} {K : NNReal} {r : ℝ}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (hr : 0 ≤ r) :
    0 ≤ gaussianGap r f := by
  have hz : (0 : Space d) ∈ Metric.closedBall 0 r := by simpa using hr
  have hb := ((isCompact_closedBall (0 : Space d) r).image hf.continuous).bddBelow
  have hmin := csInf_le hb (Set.mem_image_of_mem f hz)
  have hmean := gaussianMean_ge_value_zero hf hc
  unfold gaussianGap
  linarith

/-- The actual loss comparator is controlled by the surrogate's value and differential at zero. -/
private theorem gaussianGap_le_surrogate_support {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    {r lambda : ℝ} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hr : 0 ≤ r) (hl : 0 < lambda) (hl1 : lambda ≤ 1)
    (hgd : DifferentiableAt ℝ (surrogate lambda f) 0) :
    gaussianGap r f ≤ gaussianMean f - surrogate lambda f 0 +
      r * ‖fderiv ℝ (surrogate lambda f) 0‖ := by
  have hz : (0 : Space d) ∈ Metric.closedBall 0 r := by simpa using hr
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall (0 : Space d) r).exists_sInf_image_eq
    ⟨0, hz⟩ hf.continuous.continuousOn
  have hxn : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hsup := convex_supporting_fderiv (surrogate_convex hf hc hl) hgd.hasFDerivAt x
  simp only [sub_zero] at hsup
  have hgfx := surrogate_le hf hc hl hl1 x
  have hd := (fderiv ℝ (surrogate lambda f) 0).le_opNorm x
  have hd' := (neg_le_abs ((fderiv ℝ (surrogate lambda f) 0) x)).trans
    (by simpa only [Real.norm_eq_abs] using hd)
  have hn : ‖fderiv ℝ (surrogate lambda f) 0‖ * ‖x‖ ≤
      r * ‖fderiv ℝ (surrogate lambda f) 0‖ := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxn
      (norm_nonneg (fderiv ℝ (surrogate lambda f) 0))
  unfold gaussianGap
  rw [hmin]
  linarith

/-- Convexity controls the loss in Gaussian averaging under a radial contraction. -/
private theorem gaussianMean_sub_surrogate_zero_le_radial_derivative {d : ℕ}
    {f : Space d → ℝ} {K : NNReal} {lambda : ℝ}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 1 f) (hl : 0 < lambda) :
    gaussianMean f - surrogate lambda f 0 ≤
      ∫ x, fderiv ℝ f x x ∂gaussian d := by
  have hdiff := hs.differentiable (by norm_num)
  have hi : Integrable (fun x : Space d => fderiv ℝ f x x) (gaussian d) := by
    apply Integrable.mono' ((IsGaussian.integrable_fun_id (μ := gaussian d)).norm.const_mul (K : ℝ))
      (by fun_prop)
    filter_upwards with x
    exact ((fderiv ℝ f x).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg x))
  have hfi := integrable_lipschitz_gaussian hf
  have hfa : Integrable (fun x : Space d => f ((1 - lambda) • x)) (gaussian d) := by
    simpa using integrable_lipschitz_gaussian_affine hf (1 - lambda) 0
  have hp (x : Space d) : f x - f ((1 - lambda) • x) ≤ lambda * fderiv ℝ f x x := by
    have h := convex_supporting_fderiv hc (hdiff x).hasFDerivAt ((1 - lambda) • x)
    have heq : (1 - lambda) • x - x = (-lambda) • x := by module
    rw [heq, map_smul, smul_eq_mul] at h
    linarith
  have h := integral_mono (hfi.sub hfa) (hi.const_mul lambda) hp
  change (∫ x, f x - f ((1 - lambda) • x) ∂gaussian d) ≤
    ∫ x, lambda * fderiv ℝ f x x ∂gaussian d at h
  rw [integral_sub hfi hfa, integral_const_mul] at h
  have heq : gaussianMean f - surrogate lambda f 0 =
      ((∫ x, f x ∂gaussian d) - ∫ x, f ((1 - lambda) • x) ∂gaussian d) / lambda := by
    simp only [surrogate, gaussianMean, smul_zero, add_zero]
    ring
  rw [heq]
  exact (div_le_iff₀ hl).2 (by simpa only [mul_comm] using h)

end LG2021

end
end

/- Mollification -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

/-- Gaussian regularization of an actual function on Euclidean space. -/
private def gaussianMollify {d : ℕ} (epsilon : ℝ) (f : Space d → ℝ) (z : Space d) : ℝ :=
  ∫ x, f (z + epsilon • x) ∂gaussian d

private theorem gaussianMollify_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (epsilon : ℝ) : LipschitzWith K (gaussianMollify epsilon f) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro z w
  have hiz : Integrable (fun x : Space d => f (z + epsilon • x)) (gaussian d) := by
    simpa [add_comm] using integrable_lipschitz_gaussian_affine hf epsilon z
  have hiw : Integrable (fun x : Space d => f (w + epsilon • x)) (gaussian d) := by
    simpa [add_comm] using integrable_lipschitz_gaussian_affine hf epsilon w
  unfold gaussianMollify
  rw [← integral_sub hiz hiw]
  have hb : ∀ᵐ x : Space d ∂gaussian d,
      ‖f (z + epsilon • x) - f (w + epsilon • x)‖ ≤ (K : ℝ) * ‖z - w‖ := by
    filter_upwards with x
    simpa only [add_sub_add_right_eq_sub] using hf.norm_sub_le (z + epsilon • x)
      (w + epsilon • x)
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hb

private theorem gaussianMollify_uniform_error {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (epsilon : ℝ) (z : Space d) :
    ‖gaussianMollify epsilon f z - f z‖ ≤
      (K : ℝ) * |epsilon| * gaussianMean (fun x : Space d => ‖x‖) := by
  have hiz : Integrable (fun x : Space d => f (z + epsilon • x)) (gaussian d) := by
    simpa [add_comm] using integrable_lipschitz_gaussian_affine hf epsilon z
  have hx : Integrable (fun x : Space d => ‖x‖) (gaussian d) := by
    exact (IsGaussian.integrable_fun_id (μ := gaussian d)).norm
  have hmajor : Integrable (fun x : Space d => (K : ℝ) * |epsilon| * ‖x‖)
      (gaussian d) := hx.const_mul _
  have heq : gaussianMollify epsilon f z - f z =
      ∫ x : Space d, (f (z + epsilon • x) - f z) ∂gaussian d := by
    rw [integral_sub hiz (integrable_const _)]
    simp [gaussianMollify]
  rw [heq]
  calc
    _ ≤ ∫ x : Space d, (K : ℝ) * |epsilon| * ‖x‖ ∂gaussian d := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards with x
      have h := hf.norm_sub_le (z + epsilon • x) z
      simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_assoc] using h
    _ = _ := by rw [integral_const_mul]; rfl

private theorem gaussianMollify_convex {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (epsilon : ℝ) :
    ConvexOn ℝ Set.univ (gaussianMollify epsilon f) := by
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw a b ha hb hab
  have hi (v : Space d) : Integrable (fun x : Space d => f (v + epsilon • x))
      (gaussian d) := by
    simpa [add_comm] using integrable_lipschitz_gaussian_affine hf epsilon v
  have hp : ∀ x : Space d, f ((a • z + b • w) + epsilon • x) ≤
      a * f (z + epsilon • x) + b * f (w + epsilon • x) := by
    intro x
    have heq : a • (z + epsilon • x) + b • (w + epsilon • x) =
        (a • z + b • w) + epsilon • x := by
      calc
        _ = (a • z + b • w) + (a + b) • (epsilon • x) := by module
        _ = _ := by rw [hab, one_smul]
    simpa only [heq, smul_eq_mul] using hc.2 (Set.mem_univ (z + epsilon • x))
      (Set.mem_univ (w + epsilon • x)) ha hb hab
  have h := integral_mono (hi (a • z + b • w))
    (((hi z).const_mul a).add ((hi w).const_mul b)) hp
  change (∫ x : Space d, f ((a • z + b • w) + epsilon • x) ∂gaussian d) ≤
    ∫ x : Space d, a * f (z + epsilon • x) + b * f (w + epsilon • x) ∂gaussian d at h
  simpa only [gaussianMollify, integral_add ((hi z).const_mul a) ((hi w).const_mul b),
    integral_const_mul, smul_eq_mul] using h

/-- Gaussian regularization converges uniformly, including for nonsmooth convex functions. -/
private theorem gaussianMollify_tendstoUniformly {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) :
    TendstoUniformly (fun epsilon : ℝ => gaussianMollify epsilon f) f (𝓝 0) := by
  apply Metric.tendstoUniformly_iff.2
  intro eta heta
  have hc : Tendsto (fun epsilon : ℝ =>
      (K : ℝ) * |epsilon| * gaussianMean (fun x : Space d => ‖x‖)) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun epsilon : ℝ =>
      (K : ℝ) * |epsilon| * gaussianMean (fun x : Space d => ‖x‖)) by fun_prop).tendsto 0
  filter_upwards [(tendsto_order.1 hc).2 eta heta] with epsilon hepsilon z
  have h := (gaussianMollify_uniform_error hf epsilon z).trans_lt hepsilon
  simpa only [dist_eq_norm, norm_sub_rev] using h

end LG2021

end
end

/- SmoothingReuse -/
section
noncomputable section
namespace LG2021.ReusedSmoothing.RGF6
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma lipschitz_cont (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) : Continuous f := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) (fun x y => ?_)).continuous
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Real.coe_toNNReal _ hL] using hlip x y

private lemma nonsmooth_integrable (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x-f y| ≤ L*‖x-y‖) (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    Integrable (fun u => f (x+μ • u) • u) (stdGaussian E) := by
  have hc := lipschitz_cont f L hL hlip
  have h1 : Integrable (fun u : E => ‖u‖) (stdGaussian E) := IsGaussian.integrable_id.norm
  have h2 : Integrable (fun u : E => ‖u‖^2) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (2:ℕ) (by simp)).integrable_norm_pow (by norm_num)
  refine Integrable.mono' ((h1.const_mul |f x|).add (h2.const_mul (L*μ)))
    ((hc.comp (by fun_prop)).smul continuous_id).aestronglyMeasurable ?_
  filter_upwards [] with u
  have hh := hlip (x+μ • u) x
  rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hμ] at hh
  have hfn : |f (x+μ • u)| ≤ |f x|+L*μ*‖u‖ := by
    have htri := abs_add_le (f (x+μ • u)-f x) (f x)
    rw [sub_add_cancel] at htri
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hfn (norm_nonneg u)
  rw [norm_smul,Real.norm_eq_abs]
  dsimp only [Pi.add_apply]
  nlinarith


end LG2021.ReusedSmoothing.RGF6
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussianMollify_hasGradient {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) (z : Space d) :
    HasGradientAt (gaussianMollify epsilon f)
      (∫ u, ((f (z + epsilon • u) - f z) / epsilon) • u ∂gaussian d) z := by
  have hLip (x y : Space d) : |f x - f y| ≤ (K : ℝ) * ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y
  have heq : gaussianMollify epsilon f =
      RandomGradFree.Shared.smoothing f epsilon := rfl
  rw [heq]
  simpa only [gaussian, RandomGradFree.Nonsmooth.oracle] using
    RandomGradFree.Nonsmooth.smoothing_hasGradient f (K : ℝ) K.coe_nonneg hLip epsilon he z

end LG2021

end
end

/- Gradient -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem integrable_gaussian_affine_value_smul {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 ≤ epsilon) (z : Space d) :
    Integrable (fun u => f (z + epsilon • u) • u) (gaussian d) := by
  apply ReusedSmoothing.RGF6.nonsmooth_integrable f (K : ℝ) K.coe_nonneg
    (fun x y => ?_) epsilon he z
  simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y

private theorem gaussianMollify_hasGradient_uncentered {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) (z : Space d) :
    HasGradientAt (gaussianMollify epsilon f)
      (epsilon⁻¹ • ∫ u, f (z + epsilon • u) • u ∂gaussian d) z := by
  have hi := integrable_gaussian_affine_value_smul hf he.le z
  have hx : Integrable (fun u : Space d => u) (gaussian d) := IsGaussian.integrable_fun_id
  have heq : (fun u : Space d => ((f (z + epsilon • u) - f z) / epsilon) • u) =
      fun u => epsilon⁻¹ • (f (z + epsilon • u) • u - f z • u) := by
    funext u
    simp only [div_eq_mul_inv, smul_sub, smul_smul, ← sub_smul]
    congr 1
    ring
  have h := gaussianMollify_hasGradient hf he z
  have hic : Integrable (fun u : Space d => f z • u) (gaussian d) := hx.smul (f z)
  rw [heq, integral_smul, integral_sub hi hic, integral_smul] at h
  simpa only [gaussian, integral_id_stdGaussian, smul_zero, sub_zero] using h

private theorem surrogate_hasFDerivAt {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0) (hl1 : lambda < 1)
    (z : Space d) :
    HasFDerivAt (surrogate lambda f)
      (InnerProductSpace.toDual ℝ (Space d)
        ((1-lambda)⁻¹ • ∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d)) z := by
  let A := InnerProductSpace.toDual ℝ (Space d)
    ((1-lambda)⁻¹ • ∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d)
  have h := (gaussianMollify_hasGradient_uncentered hf (sub_pos.mpr hl1)
    (lambda • z)).hasFDerivAt
  have hc := h.comp z ((hasFDerivAt_id z).const_smul lambda)
  have hh := (((hc.sub_const (gaussianMean f)).const_mul lambda⁻¹).const_add (gaussianMean f))
  have heq : (fun y => gaussianMean f +
      lambda⁻¹ * (gaussianMollify (1-lambda) f (lambda • y) - gaussianMean f)) =
      surrogate lambda f := by
    ext y
    simp only [surrogate, gaussianMollify, add_comm]
    ring
  change HasFDerivAt (fun y => gaussianMean f +
      lambda⁻¹ * (gaussianMollify (1-lambda) f (lambda • y) - gaussianMean f))
      (lambda⁻¹ • A.comp (lambda • ContinuousLinearMap.id ℝ (Space d))) z at hh
  rw [heq] at hh
  have heqD : lambda⁻¹ • A.comp (lambda • ContinuousLinearMap.id ℝ (Space d)) = A := by
    ext v
    simp [ContinuousLinearMap.comp_apply, hl]
  rw [heqD] at hh
  exact hh

private theorem surrogate_directional_gradient {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0) (hl1 : lambda < 1)
    (z eta : Space d) :
    fderiv ℝ (surrogate lambda f) z eta = ((1-lambda)⁻¹)^2 *
      ∫ x, inner ℝ (x-lambda • z) eta * f x *
        Concentration.likelihoodRatio lambda z x ∂gaussian d := by
  have hchange := integral_likelihoodRatio hl1 z
    (F := fun x => inner ℝ (x-lambda • z) eta * f x)
    (by exact (Continuous.mul (by fun_prop) hf.continuous).measurable)
  have hi := integrable_gaussian_affine_value_smul hf (sub_pos.mpr hl1).le (lambda • z)
  rw [(surrogate_hasFDerivAt hf hl hl1 z).fderiv]
  simp only [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply, real_inner_smul_left]
  have hinner : inner ℝ (∫ u, f (lambda • z + (1-lambda) • u) • u ∂gaussian d) eta =
      ∫ u, f (lambda • z + (1-lambda) • u) * inner ℝ u eta ∂gaussian d := by
    rw [real_inner_comm, ← integral_inner hi]
    simp only [inner_smul_right, real_inner_comm]
  rw [hinner]
  have heq : (∫ x, inner ℝ (x-lambda • z) eta * f x *
      Concentration.likelihoodRatio lambda z x ∂gaussian d) =
      (1-lambda) * ∫ u, f (lambda • z + (1-lambda) • u) * inner ℝ u eta ∂gaussian d := by
    calc
      _ = ∫ x, Concentration.likelihoodRatio lambda z x *
          (inner ℝ (x-lambda • z) eta * f x) ∂gaussian d := by
        congr 1; funext x; ring
      _ = _ := by
        rw [hchange, ← integral_const_mul]
        congr 1
        funext u
        simp only [add_sub_cancel_right, real_inner_smul_left]
        rw [add_comm ((1-lambda) • u)]
        ring
  rw [heq]
  field_simp
  <;> ring

end LG2021

end
end

/- CurvatureMatrix -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem integrable_secondPartialDerivative {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f)) (i j : Fin d) :
    Integrable (secondPartialDerivative f i j) (gaussian d) := by
  apply gaussian_integrable_bounded
    (((hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      (by norm_num) |>.clm_apply continuous_const |>.aestronglyMeasurable)
    (B := (J : ℝ))
  exact norm_partialDerivative_le (partialDerivative_lipschitz hg i) j

private theorem curvatureMatrix_isHermitian {d : ℕ} (f : Space d → ℝ) :
    (curvatureMatrix f).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [curvatureMatrix, star_trivial]
  congr 1
  funext x
  simp only [mul_comm (x i) (x j), eq_comm]

private theorem second_fderiv_quadratic_sum {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (x v : Space d) :
    fderiv ℝ (fderiv ℝ f) x v v =
      ∑ i, ∑ j, v i * secondPartialDerivative f i j x * v j := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let A := fderiv ℝ (fderiv ℝ f) x
  have hv : v = ∑ i, v i • e i := (e.sum_repr v).symm
  calc
    _ = A (∑ j, v j • e j) (∑ i, v i • e i) := by rw [← hv]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [secondPartialDerivative_eq hs]
      dsimp only [A, e]
      ring

private def hessianMatrix {d : ℕ} (f : Space d → ℝ) (x : Space d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => secondPartialDerivative f i j x

private theorem hessianMatrix_quadraticForm {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (x v : Space d) :
    quadraticForm (hessianMatrix f x) v = fderiv ℝ (fderiv ℝ f) x v v :=
  (second_fderiv_quadratic_sum hs x v).symm

private theorem hessianMatrix_posSemidef {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f) (x : Space d) :
    (hessianMatrix f x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.2
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [hessianMatrix, star_trivial, secondPartialDerivative_eq hs]
    exact hs.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _
  · intro v
    have h := convex_second_fderiv_nonneg hc hs x (WithLp.toLp 2 v)
    rw [← hessianMatrix_quadraticForm hs] at h
    simpa only [quadraticForm, dotProduct, Matrix.mulVec, star_trivial,
      Finset.mul_sum, mul_assoc] using h

private theorem curvatureMatrix_quadraticForm {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) (v : Space d) :
    quadraticForm (curvatureMatrix f) v =
      ∫ x, fderiv ℝ (fderiv ℝ f) x v v ∂gaussian d := by
  simp_rw [second_fderiv_quadratic_sum hs]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ =>
    ((integrable_secondPartialDerivative hs hg i j).const_mul (v i)).mul_const (v j)))]
  unfold quadraticForm
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ =>
    ((integrable_secondPartialDerivative hs hg i j).const_mul (v i)).mul_const (v j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_mul_const, integral_const_mul, gaussian_second_partial_identity_lipschitz hf hs hg]

private theorem curvatureMatrix_posSemidef {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) : (curvatureMatrix f).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.2
  refine ⟨curvatureMatrix_isHermitian f, ?_⟩
  intro v
  have h : 0 ≤ ∫ x, fderiv ℝ (fderiv ℝ f) x (WithLp.toLp 2 v) (WithLp.toLp 2 v) ∂gaussian d :=
    integral_nonneg (fun x => convex_second_fderiv_nonneg hc hs x (WithLp.toLp 2 v))
  rw [← curvatureMatrix_quadraticForm hf hs hg] at h
  simpa only [quadraticForm, dotProduct, Matrix.mulVec, star_trivial,
    Finset.mul_sum, mul_assoc] using h

private theorem curvatureMatrix_trace {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) :
    Matrix.trace (curvatureMatrix f) = ∫ x, laplacian f x ∂gaussian d := by
  unfold laplacian Matrix.trace
  rw [integral_finsetSum _ (fun i _ => integrable_secondPartialDerivative hs hg i i)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (gaussian_second_partial_identity_lipschitz hf hs hg i i).symm

private theorem gaussian_radial_derivative_eq_trace {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) :
    (∫ x, fderiv ℝ f x x ∂gaussian d) = Matrix.trace (curvatureMatrix f) := by
  rw [curvatureMatrix_trace hf hs hg]
  simp_rw [fderiv_radial_eq_sum]
  unfold laplacian
  rw [integral_finsetSum _ (fun i _ => integrable_gaussian_coordinate_mul_lipschitz
    (partialDerivative_lipschitz hg i) i),
    integral_finsetSum _ (fun i _ => integrable_secondPartialDerivative hs hg i i)]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : ContDiff ℝ 1 (partialDerivative f i) :=
    (hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (gaussian_coordinate_integration_by_parts i
    (fun x => (hp.differentiable (by norm_num) x).hasFDerivAt)
    (integrable_lipschitz_gaussian (partialDerivative_lipschitz hg i))
    (integrable_secondPartialDerivative hs hg i i)
    (integrable_gaussian_coordinate_mul_lipschitz (partialDerivative_lipschitz hg i) i)).symm

private theorem gaussianGap_le_trace_add_surrogate_gradient {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} {r lambda : ℝ} (hf : LipschitzWith K f)
    (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) (hr : 0 ≤ r)
    (hl : 0 < lambda) (hl1 : lambda < 1) :
    gaussianGap r f ≤ Matrix.trace (curvatureMatrix f) +
      r * ‖fderiv ℝ (surrogate lambda f) 0‖ := by
  have h1 := gaussianGap_le_surrogate_support hf hc hr hl hl1.le
    (surrogate_hasFDerivAt hf hl.ne' hl1 0).differentiableAt
  have h2 := gaussianMean_sub_surrogate_zero_le_radial_derivative hf hc
    (hs.of_le (by norm_num)) hl
  rw [gaussian_radial_derivative_eq_trace hf hs hg] at h2
  linarith

end LG2021

end
end

/- Cutoff -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology

/-- Increasing smooth approximation to the indicator outside a Euclidean ball. -/
private def radialCutoff {d : ℕ} (B : ℝ) (n : ℕ) (x : Space d) : ℝ :=
  Real.smoothTransition (((n : ℝ)+1) * (‖x‖^2-B^2))

private theorem radialCutoff_nonneg {d : ℕ} (B : ℝ) (n : ℕ) (x : Space d) :
    0 ≤ radialCutoff B n x := Real.smoothTransition.nonneg _

private theorem radialCutoff_le_one {d : ℕ} (B : ℝ) (n : ℕ) (x : Space d) :
    radialCutoff B n x ≤ 1 := Real.smoothTransition.le_one _

private theorem radialCutoff_contDiff {d : ℕ} (B : ℝ) (n : ℕ) (k : ℕ∞) :
    ContDiff ℝ k (@radialCutoff d B n) := by
  unfold radialCutoff
  have hnorm : ContDiff ℝ k (fun x : Space d => ‖x‖^2) := contDiff_norm_sq ℝ
  exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (hnorm.sub contDiff_const))

private theorem radialCutoff_hasFDerivAt {d : ℕ} (B : ℝ) (n : ℕ) (x : Space d) :
    HasFDerivAt (radialCutoff B n)
      ((2*((n : ℝ)+1)*deriv Real.smoothTransition (((n : ℝ)+1)*(‖x‖^2-B^2))) •
        innerSL ℝ x) x := by
  have ht := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
  have h := (ht (((n : ℝ)+1)*(‖x‖^2-B^2))).hasDerivAt.comp_hasFDerivAt x
    (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const (B^2)).const_mul ((n : ℝ)+1))
  convert! h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem radialCutoff_deriv_coefficient_nonneg {d : ℕ} (B : ℝ) (n : ℕ) (x : Space d) :
    0 ≤ 2*((n : ℝ)+1)*deriv Real.smoothTransition (((n : ℝ)+1)*(‖x‖^2-B^2)) := by
  have h := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) (((n : ℝ)+1)*(‖x‖^2-B^2))).hasDerivAt
    |>.nonneg_of_monotone Real.smoothTransition.monotone
  positivity

private theorem radialCutoff_zero_of_norm_le {d : ℕ} {B : ℝ} (hB : 0 ≤ B) (n : ℕ)
    {x : Space d} (hx : ‖x‖ ≤ B) : radialCutoff B n x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  nlinarith [norm_nonneg x]

private theorem radialCutoff_complement_hasCompactSupport {d : ℕ} (B : ℝ) (n : ℕ) :
    HasCompactSupport (fun x : Space d => 1-radialCutoff B n x) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Space d) (Real.sqrt (B^2+1)))
    Metric.isClosed_closedBall
  intro x hx
  have hx' : Real.sqrt (B^2+1) < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have harg : 1 ≤ ((n : ℝ)+1)*(‖x‖^2-B^2) := by
    have hs := Real.sq_sqrt (show 0 ≤ B^2+1 by positivity)
    have hh : 1 < ‖x‖^2-B^2 := by nlinarith [Real.sqrt_nonneg (B^2+1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [radialCutoff, Real.smoothTransition.one_of_one_le harg, sub_self]

private theorem radialCutoff_fderiv_bounded {d : ℕ} (B : ℝ) (n : ℕ) :
    ∃ C : ℝ, ∀ x : Space d, ‖fderiv ℝ (radialCutoff B n) x‖ ≤ C := by
  have hs := radialCutoff_contDiff (d := d) B n 1
  have ht : ContDiff ℝ 1 (fun x : Space d => 1-radialCutoff B n x) := contDiff_const.sub hs
  obtain ⟨C,hC⟩ := ((radialCutoff_complement_hasCompactSupport (d := d) B n).fderiv ℝ).exists_bound_of_continuous (ht.continuous_fderiv (by norm_num))
  refine ⟨C, fun x => ?_⟩
  have heq := ((hs.differentiable (by norm_num) x).hasFDerivAt.const_sub 1).fderiv
  simpa only [heq, norm_neg] using hC x

private theorem radialCutoff_tendsto {d : ℕ} {B : ℝ} (hB : 0 ≤ B) (x : Space d) :
    Tendsto (fun n => radialCutoff B n x) atTop
      (𝓝 (if B < ‖x‖ then 1 else 0)) := by
  by_cases hx : B < ‖x‖
  · have hp : 0 < ‖x‖^2-B^2 := by nlinarith [norm_nonneg x]
    have ht : Tendsto (fun n : ℕ => ((n : ℝ)+1)*(‖x‖^2-B^2)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const hp
    have hev : ∀ᶠ n : ℕ in atTop, radialCutoff B n x = 1 := by
      filter_upwards [ht.eventually_ge_atTop 1] with n hn
      exact Real.smoothTransition.one_of_one_le hn
    simpa only [if_pos hx] using tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)
  · have hev : (fun n => radialCutoff B n x) = fun _ => 0 := by
      funext n
      exact radialCutoff_zero_of_norm_le hB n (le_of_not_gt hx)
    simp only [hev, if_neg hx]
    exact tendsto_const_nhds

end LG2021

end
end

/- WeightedStein -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem weighted_laplacian_le {d : ℕ} {f chi : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) (hchi : ContDiff ℝ 1 chi)
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    {C : ℝ} (hC : ∀ x, ‖fderiv ℝ chi x‖ ≤ C)
    (hcross : ∀ x, 0 ≤ ∑ i, partialDerivative chi i x * partialDerivative f i x) :
    (∫ x, chi x * laplacian f x ∂gaussian d) ≤
      (K : ℝ) * ∫ x, chi x * ‖x‖ ∂gaussian d := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let P (i : Fin d) (x : Space d) : Space d →L[ℝ] ℝ :=
    chi x • fderiv ℝ (partialDerivative f i) x +
      partialDerivative f i x • fderiv ℝ chi x
  have hc : Continuous chi := hchi.continuous
  have hcd : Continuous (fderiv ℝ chi) := hchi.continuous_fderiv (by norm_num)
  have hp (i : Fin d) : ContDiff ℝ 1 (partialDerivative f i) :=
    (hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hchin (x : Space d) : ‖chi x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hchi0 x)]
    exact hchi1 x
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ chi 0)).trans (hC 0)
  have hPnorm (i : Fin d) (x : Space d) : ‖P i x‖ ≤ (J : ℝ) + K*C := by
    calc
      _ ≤ ‖chi x • fderiv ℝ (partialDerivative f i) x‖ +
          ‖partialDerivative f i x • fderiv ℝ chi x‖ := norm_add_le _ _
      _ ≤ 1 * (J : ℝ) + (K : ℝ)*C := by
        simp only [norm_smul]
        apply add_le_add
        · exact mul_le_mul (hchin x)
            (norm_fderiv_le_of_lipschitz ℝ (partialDerivative_lipschitz hg i))
            (norm_nonneg _) zero_le_one
        · exact mul_le_mul (norm_partialDerivative_le hf i x) (hC x)
            (norm_nonneg _) K.coe_nonneg
      _ = _ := by ring
  have hPcont (i : Fin d) : Continuous (P i) := by
    exact (hc.smul ((hp i).continuous_fderiv (by norm_num))).add
      ((hp i).continuous.smul hcd)
  have hPderiv (i : Fin d) (x : Space d) :
      HasFDerivAt (fun y => chi y * partialDerivative f i y) (P i x) x := by
    exact ((hchi.differentiable (by norm_num) x).hasFDerivAt).mul
      (((hp i).differentiable (by norm_num) x).hasFDerivAt)
  have hPi (i : Fin d) : Integrable (fun x => P i x (e i)) (gaussian d) := by
    apply gaussian_integrable_bounded ((hPcont i).clm_apply continuous_const |>.aestronglyMeasurable)
      (B := (J : ℝ)+K*C)
    intro x
    calc
      _ ≤ ‖P i x‖ * ‖e i‖ := (P i x).le_opNorm _
      _ ≤ _ := by rw [e.orthonormal.norm_eq_one i, mul_one]; exact hPnorm i x
  have hXi (i : Fin d) : Integrable (fun x : Space d => x i * (chi x * partialDerivative f i x))
      (gaussian d) := by
    apply Integrable.mono' ((integrable_gaussian_norm_pow d 1).const_mul (K : ℝ))
      (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).mul
        (hc.mul (hp i).continuous)).aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, norm_mul, pow_one]
    calc
      ‖x i‖ * (‖chi x‖ * ‖partialDerivative f i x‖) ≤ ‖x‖ * (1*(K : ℝ)) := by
        gcongr
        · exact PiLp.norm_apply_le x i
        · exact hchin x
        · exact norm_partialDerivative_le hf i x
      _ = _ := by ring
  have hIBP (i : Fin d) : (∫ x, P i x (e i) ∂gaussian d) =
      ∫ x, x i * (chi x * partialDerivative f i x) ∂gaussian d := by
    apply gaussian_coordinate_integration_by_parts i (hPderiv i)
    · apply gaussian_integrable_bounded (hc.mul (hp i).continuous |>.aestronglyMeasurable)
        (B := (K : ℝ))
      intro x
      rw [Pi.mul_apply, norm_mul]
      calc
        _ ≤ 1*(K : ℝ) := mul_le_mul (hchin x) (norm_partialDerivative_le hf i x)
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · exact hPi i
    · exact hXi i
  have hsum : (∫ x, ∑ i, P i x (e i) ∂gaussian d) =
      ∫ x, chi x * fderiv ℝ f x x ∂gaussian d := by
    rw [integral_finset_sum _ (fun i _ => hPi i)]
    simp_rw [hIBP]
    rw [← integral_finset_sum _ (fun i _ => hXi i)]
    congr 1
    funext x
    rw [fderiv_radial_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlap : Integrable (fun x => chi x * laplacian f x) (gaussian d) := by
    apply gaussian_integrable_bounded (hc.mul (laplacian_continuous hs) |>.aestronglyMeasurable)
      (B := (d : ℝ)*J)
    intro x
    rw [Pi.mul_apply, norm_mul]
    calc
      _ ≤ 1*((d : ℝ)*J) := mul_le_mul (hchin x) (norm_laplacian_le hg x)
        (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hrad : Integrable (fun x => chi x * fderiv ℝ f x x) (gaussian d) := by
    have := integrable_finset_sum Finset.univ (fun i _ => hXi i)
    convert! this using 1
    funext x
    rw [fderiv_radial_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hnorm : Integrable (fun x => chi x * ‖x‖) (gaussian d) := by
    apply (integrable_gaussian_norm_pow d 1).mono' (by fun_prop)
    filter_upwards with x
    simpa only [norm_mul, norm_norm, pow_one, one_mul] using
      mul_le_mul_of_nonneg_right (hchin x) (norm_nonneg x)
  calc
    _ ≤ ∫ x, ∑ i, P i x (e i) ∂gaussian d := by
      apply integral_mono hlap (integrable_finset_sum Finset.univ (fun i _ => hPi i))
      intro x
      have heq : (∑ i, P i x (e i)) = chi x * laplacian f x +
          ∑ i, partialDerivative chi i x * partialDerivative f i x := by
        simp only [P, add_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          laplacian, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        unfold partialDerivative
        ring
      dsimp only
      rw [heq]
      exact le_add_of_nonneg_right (hcross x)
    _ = ∫ x, chi x * fderiv ℝ f x x ∂gaussian d := hsum
    _ ≤ ∫ x, (K : ℝ) * (chi x * ‖x‖) ∂gaussian d := by
      apply integral_mono hrad (hnorm.const_mul _)
      intro x
      have hb : fderiv ℝ f x x ≤ (K : ℝ) * ‖x‖ :=
        (le_abs_self _).trans (((fderiv ℝ f x).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg x)))
      have hh := mul_le_mul_of_nonneg_left hb (hchi0 x)
      nlinarith
    _ = _ := integral_const_mul _ _

end LG2021

end
end

/- HessianTail -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology

private theorem convex_radial_fderiv_nonneg {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : Differentiable ℝ f)
    (hmin : ∀ x, f 0 ≤ f x) (x : Space d) : 0 ≤ fderiv ℝ f x x := by
  have h := convex_supporting_fderiv hc (hs x).hasFDerivAt 0
  simp only [zero_sub, map_neg] at h
  linarith [hmin x]

private theorem radialCutoff_cross_nonneg {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : Differentiable ℝ f)
    (hmin : ∀ x, f 0 ≤ f x) (B : ℝ) (n : ℕ) (x : Space d) :
    0 ≤ ∑ i, partialDerivative (radialCutoff B n) i x * partialDerivative f i x := by
  let c := 2*((n : ℝ)+1)*deriv Real.smoothTransition (((n : ℝ)+1)*(‖x‖^2-B^2))
  have heq : (∑ i, partialDerivative (radialCutoff B n) i x * partialDerivative f i x) =
      c * fderiv ℝ f x x := by
    rw [fderiv_radial_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change ((fderiv ℝ (radialCutoff B n) x) (EuclideanSpace.basisFun (Fin d) ℝ i)) * _ = _
    rw [(radialCutoff_hasFDerivAt B n x).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, EuclideanSpace.inner_basisFun_real]
    dsimp only [c]
    ring
  rw [heq]
  exact mul_nonneg (radialCutoff_deriv_coefficient_nonneg B n x)
    (convex_radial_fderiv_nonneg hc hs hmin x)

private theorem radialCutoff_integral_tendsto {d : ℕ} {B : ℝ} (hB : 0 ≤ B)
    {F : Space d → ℝ} (hF : Integrable F (gaussian d)) :
    Tendsto (fun n => ∫ x, radialCutoff B n x * F x ∂gaussian d) atTop
      (𝓝 (∫ x in {x : Space d | B < ‖x‖}, F x ∂gaussian d)) := by
  have hmeas : MeasurableSet {x : Space d | B < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  rw [← integral_indicator hmeas]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
  · intro n
    exact (radialCutoff_contDiff B n 0).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · exact hF.norm
  · intro n
    filter_upwards with x
    rw [norm_mul, Real.norm_of_nonneg (radialCutoff_nonneg B n x)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (radialCutoff_le_one B n x) (norm_nonneg (F x))
  · filter_upwards with x
    have h := (radialCutoff_tendsto hB x).mul_const (F x)
    simpa only [Set.indicator, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul] using h

/-- Convexity makes the radial-cutoff derivative term nonnegative. Consequently the
exterior Hessian trace is controlled by the first Gaussian moment on the same exterior set. -/
private theorem gaussian_laplacian_tail_le {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) (hmin : ∀ x, f 0 ≤ f x)
    {B : ℝ} (hB : 0 ≤ B) :
    (∫ x in {x : Space d | B < ‖x‖}, laplacian f x ∂gaussian d) ≤
      (K : ℝ) * ∫ x in {x : Space d | B < ‖x‖}, ‖x‖ ∂gaussian d := by
  have hlap : Integrable (laplacian f) (gaussian d) :=
    gaussian_integrable_bounded (laplacian_continuous hs).aestronglyMeasurable
      (norm_laplacian_le hg)
  have hnorm : Integrable (fun x : Space d => ‖x‖) (gaussian d) := by
    simpa only [pow_one] using integrable_gaussian_norm_pow d 1
  apply le_of_tendsto_of_tendsto (radialCutoff_integral_tendsto hB hlap)
    ((radialCutoff_integral_tendsto hB hnorm).const_mul (K : ℝ))
  filter_upwards with n
  obtain ⟨C,hC⟩ := radialCutoff_fderiv_bounded (d := d) B n
  exact weighted_laplacian_le hf hs hg (radialCutoff_contDiff B n 1)
    (radialCutoff_nonneg B n) (radialCutoff_le_one B n) hC
    (radialCutoff_cross_nonneg hc (hs.differentiable (by norm_num)) hmin B n)

end LG2021

end
end

/- LG2021GaussianMoments -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal

private theorem gaussian_inner_law {d : ℕ} (q : Space d) :
    (gaussian d).map (fun x => inner ℝ q x) = gaussianReal 0 (‖q‖ ^ 2).toNNReal := by
  change (stdGaussian (Space d)).map (innerSL ℝ q) = _
  rw [IsGaussian.map_eq_gaussianReal]
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm]

private theorem gaussian_inner_hasSubgaussianMGF {d : ℕ} (q : Space d) :
    HasSubgaussianMGF (fun x => inner ℝ q x) (‖q‖ ^ 2).toNNReal (gaussian d) := by
  apply (HasSubgaussianMGF.id_map_iff (by fun_prop)).1
  rw [gaussian_inner_law]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  simp [mgf_id_gaussianReal]

private theorem gaussian_inner_map {d : ℕ} (q : Space d) :
    (gaussian d).map (fun x => inner ℝ q x) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖q‖ * x) := by
  calc
    _ = gaussianReal 0 (‖q‖ ^ 2).toNNReal := by
      change (stdGaussian (Space d)).map (innerSL ℝ q) = _
      rw [IsGaussian.map_eq_gaussianReal]
      simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
        innerSL_apply_norm]
    _ = _ := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        simp

private theorem gaussian_inner_second_moment {d : ℕ} (q : Space d) :
    (∫ x, (inner ℝ q x) ^ 2 ∂gaussian d) = ‖q‖ ^ 2 := by
  have hmean : (∫ x : Space d, inner ℝ q x ∂stdGaussian (Space d)) = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ q)
  have hvar := variance_eq_integral (μ := stdGaussian (Space d))
    (X := fun x => inner ℝ q x) (by fun_prop)
  rw [hmean] at hvar
  simp only [sub_zero] at hvar
  change (∫ x : Space d, (inner ℝ q x) ^ 2 ∂stdGaussian (Space d)) = _
  rw [← hvar]
  have heq : (fun x : Space d => inner ℝ q x) = (innerSL ℝ q : Space d → ℝ) := rfl
  rw [heq, variance_dual_stdGaussian, innerSL_apply_norm]

private theorem gaussian_inner_fourth_moment {d : ℕ} (q : Space d) :
    (∫ x, (inner ℝ q x) ^ 4 ∂gaussian d) = 3 * ‖q‖ ^ 4 := by
  calc
    _ = ∫ y : ℝ, y ^ 4 ∂((gaussian d).map (fun x => inner ℝ q x)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ y : ℝ, (‖q‖ * y) ^ 4 ∂gaussianReal 0 1 := by
      rw [gaussian_inner_map, integral_map (by fun_prop) (by fun_prop)]
    _ = _ := by
      simp only [mul_pow, integral_const_mul, OAI.IndependentProducts.gaussian_integral_fourth]
      ring

private theorem gaussian_coord_second_moment {d : ℕ} (i : Fin d) :
    (∫ x : Space d, (x i) ^ 2 ∂gaussian d) = 1 := by
  simpa [EuclideanSpace.inner_single_left] using
    gaussian_inner_second_moment (EuclideanSpace.single i (1 : ℝ))

private theorem gaussian_coord_fourth_moment {d : ℕ} (i : Fin d) :
    (∫ x : Space d, (x i) ^ 4 ∂gaussian d) = 3 := by
  simpa [EuclideanSpace.inner_single_left] using
    gaussian_inner_fourth_moment (EuclideanSpace.single i (1 : ℝ))

private theorem gaussian_coord_sq_integrable {d : ℕ} (i : Fin d) :
    Integrable (fun x : Space d => (x i) ^ 2) (gaussian d) := by
  have h := (IsGaussian.memLp_dual (gaussian d)
    (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) 2 (by norm_num)).integrable_sq
  have heq : (fun x : Space d =>
      ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x) ^ 2) = fun x => (x i) ^ 2 := by
    funext x
    simp [EuclideanSpace.inner_single_left]
  simpa only [heq] using h

private theorem gaussian_coord_fourth_integrable {d : ℕ} (i : Fin d) :
    Integrable (fun x : Space d => (x i) ^ 4) (gaussian d) := by
  have h := (IsGaussian.memLp_dual (gaussian d)
    (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) 4 (by norm_num)).integrable_norm_pow
      (by norm_num : (4 : ℕ) ≠ 0)
  have heq : (fun x : Space d =>
      ‖(innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) x‖ ^ 4) = fun x => (x i) ^ 4 := by
    funext x
    simp only [innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
      Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
  simpa only [heq] using h

private theorem gaussian_norm_sq_integrable (d : ℕ) :
    Integrable (fun x : Space d => ‖x‖ ^ 2) (gaussian d) := by
  simpa using (IsGaussian.memLp_id (gaussian d) 2 (by norm_num)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)

private theorem gaussian_norm_fourth_integrable (d : ℕ) :
    Integrable (fun x : Space d => ‖x‖ ^ 4) (gaussian d) := by
  simpa using (IsGaussian.memLp_id (gaussian d) 4 (by norm_num)).integrable_norm_pow
    (by norm_num : (4 : ℕ) ≠ 0)

private theorem gaussian_norm_second_moment (d : ℕ) :
    (∫ x : Space d, ‖x‖ ^ 2 ∂gaussian d) = d := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => gaussian_coord_sq_integrable i)]
  simp [gaussian_coord_second_moment]

private theorem gaussian_norm_fourth_moment_le (d : ℕ) :
    (∫ x : Space d, ‖x‖ ^ 4 ∂gaussian d) ≤ 3 * (d : ℝ) ^ 2 := by
  have hpoint (x : Space d) : ‖x‖ ^ 4 ≤ (d : ℝ) * ∑ i, (x i) ^ 4 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin d => (x i) ^ 2) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    rw [show ‖x‖ ^ 4 = (‖x‖ ^ 2) ^ 2 by ring, EuclideanSpace.real_norm_sq_eq]
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num, mul_comm] using h
  calc
    _ ≤ ∫ x : Space d, (d : ℝ) * ∑ i, (x i) ^ 4 ∂gaussian d :=
      integral_mono (gaussian_norm_fourth_integrable d)
        ((integrable_finsetSum Finset.univ
          (fun i _ => gaussian_coord_fourth_integrable i)).const_mul (d : ℝ)) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => gaussian_coord_fourth_integrable i)]
      simp [gaussian_coord_fourth_moment]
      ring

end LG2021

end
end

/- TailMoment -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussian_setIntegral_norm_le {d : ℕ} {A : Set (Space d)} (hA : MeasurableSet A) :
    (∫ x in A, ‖x‖ ∂gaussian d) ≤ Real.sqrt ((d : ℝ) * (gaussian d).real A) := by
  have hX : MemLp (fun x : Space d => ‖x‖) (ENNReal.ofReal 2) (gaussian d) := by
    simpa only [ENNReal.ofReal_ofNat, id_eq] using (IsGaussian.memLp_id (gaussian d) 2 (by norm_num)).norm
  have hI : MemLp (A.indicator (fun _ : Space d => (1 : ℝ))) (ENNReal.ofReal 2) (gaussian d) :=
    (memLp_const 1).indicator hA
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x : Space d => norm_nonneg x))
    (Filter.Eventually.of_forall (fun x : Space d => by
      by_cases hx : x ∈ A <;> simp [Set.indicator, hx])) hX hI
  have heq : (fun x : Space d => ‖x‖ * A.indicator (fun _ => (1 : ℝ)) x) =
      A.indicator (fun x : Space d => ‖x‖) := by
    funext x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  have heq2 : (fun x : Space d => (A.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ)) =
      A.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
  rw [heq, integral_indicator hA, heq2, integral_indicator hA] at h
  simp only [Real.rpow_two, gaussian_norm_second_moment, integral_const,
    Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] at h
  simpa only [Real.sqrt_mul (Nat.cast_nonneg d), Measure.real] using h

private theorem gaussian_laplacian_tail_le_sqrt {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) (hmin : ∀ x, f 0 ≤ f x)
    {B delta : ℝ} (hB : 0 ≤ B)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta) :
    (∫ x in {x : Space d | B < ‖x‖}, laplacian f x ∂gaussian d) ≤
      (K : ℝ) * Real.sqrt ((d : ℝ) * delta) := by
  calc
    _ ≤ (K : ℝ) * ∫ x in {x : Space d | B < ‖x‖}, ‖x‖ ∂gaussian d :=
      gaussian_laplacian_tail_le hf hc hs hg hmin hB
    _ ≤ (K : ℝ) * Real.sqrt ((d : ℝ) * (gaussian d).real {x : Space d | B < ‖x‖}) :=
      mul_le_mul_of_nonneg_left
        (gaussian_setIntegral_norm_le (measurableSet_lt measurable_const measurable_norm)) K.coe_nonneg
    _ ≤ _ := by gcongr

end LG2021

end
end

/- Differentiate -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

/-- Differentiation commutes with Gaussian regularization for a continuously differentiable
Lipschitz loss. The domination follows from the Lipschitz constant. -/
private theorem gaussianMollify_hasFDerivAt_of_contDiff {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 1 f) (epsilon : ℝ) (z : Space d) :
    HasFDerivAt (gaussianMollify epsilon f)
      (∫ x, fderiv ℝ f (z + epsilon • x) ∂gaussian d) z := by
  have hdiff := hs.differentiable (by norm_num)
  have hcont := hs.continuous_fderiv (by norm_num)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z x : Space d => f (z + epsilon • x))
    (F' := fun z x : Space d => fderiv ℝ f (z + epsilon • x))
    (s := Set.univ) (bound := fun _ => (K : ℝ))
    Filter.univ_mem (Eventually.of_forall fun _ => by fun_prop)
  · simpa [add_comm] using integrable_lipschitz_gaussian_affine hf epsilon z
  · fun_prop
  · filter_upwards with x z hz
    exact norm_fderiv_le_of_lipschitz ℝ hf
  · exact integrable_const _
  · filter_upwards with x z hz
    have h := (hdiff (z + epsilon • x)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (epsilon • x))
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using h

end LG2021

end
end

/- Smooth -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussianMollify_gradient_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) :
    LipschitzWith (Real.toNNReal ((K : ℝ) / epsilon * gaussianMean (fun u : Space d => ‖u‖)))
      (gradient (gaussianMollify epsilon f)) := by
  have hn : 0 ≤ gaussianMean (fun u : Space d => ‖u‖) := integral_nonneg (fun _ => norm_nonneg _)
  apply lipschitzWith_iff_norm_sub_le.2
  intro z w
  rw [(gaussianMollify_hasGradient_uncentered hf he z).gradient,
    (gaussianMollify_hasGradient_uncentered hf he w).gradient, ← smul_sub,
    ← integral_sub (integrable_gaussian_affine_value_smul hf he.le z)
      (integrable_gaussian_affine_value_smul hf he.le w)]
  have hmajor : Integrable (fun u : Space d => (K : ℝ) * ‖z-w‖ * ‖u‖) (gaussian d) :=
    by
      simpa only [pow_one] using (integrable_gaussian_norm_pow d 1).const_mul ((K : ℝ) * ‖z-w‖)
  have hbound : ‖∫ u : Space d, f (z+epsilon • u) • u - f (w+epsilon • u) • u ∂gaussian d‖ ≤
      (K : ℝ) * ‖z-w‖ * gaussianMean (fun u : Space d => ‖u‖) := by
    calc
      _ ≤ ∫ u : Space d, (K : ℝ) * ‖z-w‖ * ‖u‖ ∂gaussian d := by
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards with u
        rw [← sub_smul, norm_smul]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [add_sub_add_right_eq_sub] using
            hf.norm_sub_le (z+epsilon • u) (w+epsilon • u)) (norm_nonneg u)
      _ = _ := by rw [integral_const_mul]; rfl
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr he.le),
    Real.coe_toNNReal _ (by positivity)]
  calc
    _ ≤ epsilon⁻¹ * ((K : ℝ) * ‖z-w‖ * gaussianMean (fun u : Space d => ‖u‖)) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr he.le)
    _ = _ := by ring

private theorem gaussianMollify_contDiff_one {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) :
    ContDiff ℝ 1 (gaussianMollify epsilon f) := by
  apply contDiff_one_iff_hasFDerivAt.2
  refine ⟨fun z => InnerProductSpace.toDual ℝ (Space d)
    (gradient (gaussianMollify epsilon f) z), ?_, ?_⟩
  · exact (InnerProductSpace.toDual ℝ (Space d)).continuous.comp
      (gaussianMollify_gradient_lipschitz hf he).continuous
  · intro z
    have h := gaussianMollify_hasGradient_uncentered hf he z
    dsimp only
    rw [h.gradient]
    exact h.hasFDerivAt

private theorem gaussianMollify_fderiv_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon : ℝ} (he : 0 < epsilon) :
    LipschitzWith (Real.toNNReal ((K : ℝ) / epsilon * gaussianMean (fun u : Space d => ‖u‖)))
      (fderiv ℝ (gaussianMollify epsilon f)) := by
  rw [← toDual_comp_gradient]
  simpa only [one_mul] using (InnerProductSpace.toDual ℝ (Space d)).lipschitz.comp
    (gaussianMollify_gradient_lipschitz hf he)

private theorem directional_fderiv_lipschitz {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hg : LipschitzWith J (gradient f)) (v : Space d) :
    LipschitzWith (J * ‖v‖₊) (fun x => fderiv ℝ f x v) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  rw [← toDual_gradient, ← toDual_gradient]
  simp only [InnerProductSpace.toDual_apply_apply, ← inner_sub_left]
  calc
    _ ≤ ‖gradient f x - gradient f y‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ ((J : ℝ) * ‖x-y‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (hg.norm_sub_le x y) (norm_nonneg v)
    _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring

private theorem gaussianMollify_contDiff_two_of_gradient_lipschitz {d : ℕ}
    {f : Space d → ℝ} {K J : NNReal} (hf : LipschitzWith K f)
    (hs : ContDiff ℝ 1 f) (hg : LipschitzWith J (gradient f))
    {epsilon : ℝ} (he : 0 < epsilon) : ContDiff ℝ 2 (gaussianMollify epsilon f) := by
  change ContDiff ℝ (1 + 1) (gaussianMollify epsilon f)
  apply contDiff_succ_iff_fderiv_apply.2
  refine ⟨(gaussianMollify_contDiff_one hf he).differentiable (by norm_num),
    (by simp), ?_⟩
  intro v
  have hident : (fun z => fderiv ℝ (gaussianMollify epsilon f) z v) =
      gaussianMollify epsilon (fun x => fderiv ℝ f x v) := by
    funext z
    rw [(gaussianMollify_hasFDerivAt_of_contDiff hf hs epsilon z).fderiv]
    unfold gaussianMollify
    rw [ContinuousLinearMap.integral_apply]
    apply Integrable.mono' (integrable_const (K : ℝ))
      ((hs.continuous_fderiv (by norm_num)).comp (by fun_prop)).aestronglyMeasurable
    filter_upwards with x
    exact norm_fderiv_le_of_lipschitz ℝ hf
  rw [hident]
  exact gaussianMollify_contDiff_one (directional_fderiv_lipschitz hg v) he

private theorem gaussianMollify_twice_contDiff_two {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {epsilon eta : ℝ} (he : 0 < epsilon) (ht : 0 < eta) :
    ContDiff ℝ 2 (gaussianMollify eta (gaussianMollify epsilon f)) :=
  gaussianMollify_contDiff_two_of_gradient_lipschitz
    (gaussianMollify_lipschitz hf epsilon) (gaussianMollify_contDiff_one hf he)
    (gaussianMollify_gradient_lipschitz hf he) ht

end LG2021

end
end

/- SecondDerivative -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gradient_lipschitz_of_fderiv_lipschitz {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hg : LipschitzWith J (fderiv ℝ f)) : LipschitzWith J (gradient f) := by
  have heq : gradient f = (InnerProductSpace.toDual ℝ (Space d)).symm ∘ fderiv ℝ f := rfl
  rw [heq]
  simpa only [one_mul] using (InnerProductSpace.toDual ℝ (Space d)).symm.lipschitz.comp hg

private theorem gaussianMollify_fderiv_apply {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 1 f) (epsilon : ℝ) (z v : Space d) :
    fderiv ℝ (gaussianMollify epsilon f) z v =
      gaussianMollify epsilon (fun x => fderiv ℝ f x v) z := by
  rw [(gaussianMollify_hasFDerivAt_of_contDiff hf hs epsilon z).fderiv]
  unfold gaussianMollify
  rw [ContinuousLinearMap.integral_apply]
  apply Integrable.mono' (integrable_const (K : ℝ))
    ((hs.continuous_fderiv (by norm_num)).comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  exact norm_fderiv_le_of_lipschitz ℝ hf

private theorem gaussianMollify_second_fderiv_apply {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) {epsilon : ℝ} (he : 0 < epsilon)
    (z v w : Space d) :
    fderiv ℝ (fderiv ℝ (gaussianMollify epsilon f)) z v w =
      ∫ x, fderiv ℝ (fderiv ℝ f) (z+epsilon • x) v w ∂gaussian d := by
  have hs1 : ContDiff ℝ 1 f := hs.of_le (by norm_num)
  have hsM := gaussianMollify_contDiff_two_of_gradient_lipschitz hf hs1
    (gradient_lipschitz_of_fderiv_lipschitz hg) he
  have hD := (hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDM := (hsM.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdir : LipschitzWith (J*‖w‖₊) (fun x => fderiv ℝ f x w) :=
    directional_fderiv_lipschitz (gradient_lipschitz_of_fderiv_lipschitz hg) w
  have hsdir : ContDiff ℝ 1 (fun x => fderiv ℝ f x w) :=
    (hs.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have heq : (fun y => fderiv ℝ (gaussianMollify epsilon f) y w) =
      gaussianMollify epsilon (fun y => fderiv ℝ f y w) := by
    funext y
    exact gaussianMollify_fderiv_apply hf hs1 epsilon y w
  have hleft : fderiv ℝ (fun y => fderiv ℝ (gaussianMollify epsilon f) y w) z v =
      fderiv ℝ (fderiv ℝ (gaussianMollify epsilon f)) z v w := by
    rw [fderiv_clm_apply (hDM z) (differentiableAt_const w)]
    simp
  rw [← hleft, heq, gaussianMollify_fderiv_apply hdir hsdir]
  unfold gaussianMollify
  congr 1
  funext x
  dsimp only
  rw [fderiv_clm_apply (hD _) (differentiableAt_const w)]
  simp

end LG2021

end
end

/- Sphere -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory

private theorem measurable_gaussian_normalize (d : ℕ) (R : ℝ) :
    Measurable (fun x : Space d => (R / ‖x‖) • x) := by fun_prop

private instance sphereMeasure_probability (d : ℕ) (R : ℝ) :
    IsProbabilityMeasure (sphereMeasure d R) := by
  unfold sphereMeasure
  exact Measure.isProbabilityMeasure_map (measurable_gaussian_normalize d R).aemeasurable

private theorem gaussian_map_neg (d : ℕ) :
    (gaussian d).map (fun x => -x) = gaussian d := by
  simpa only [gaussian, LinearIsometryEquiv.coe_neg] using
    (stdGaussian_map (LinearIsometryEquiv.neg ℝ : Space d ≃ₗᵢ[ℝ] Space d))

private theorem sphereMeasure_map_neg (d : ℕ) (R : ℝ) :
    (sphereMeasure d R).map (fun x => -x) = sphereMeasure d R := by
  unfold sphereMeasure
  rw [Measure.map_map (by fun_prop) (measurable_gaussian_normalize d R)]
  have heq : (fun x : Space d => -((R / ‖x‖) • x)) =
      (fun x : Space d => (R / ‖x‖) • x) ∘ (fun x => -x) := by
    funext x
    simp
  change Measure.map (fun x : Space d => -((R / ‖x‖) • x)) (gaussian d) = _
  rw [heq]
  rw [← Measure.map_map (measurable_gaussian_normalize d R) (by fun_prop), gaussian_map_neg]

private theorem sphereMeasure_neg_preimage {d : ℕ} (R : ℝ) {s : Set (Space d)}
    (hs : MeasurableSet s) :
    (sphereMeasure d R) ((fun x => -x) ⁻¹' s) = sphereMeasure d R s := by
  rw [← Measure.map_apply (by fun_prop) hs, sphereMeasure_map_neg]

/-- The precise symmetry step turning a two-sided success probability into a one-sided one. -/
private theorem sphereMeasure_one_sided_of_max {d : ℕ} (R : ℝ) {f : Space d → ℝ}
    (hf : Measurable f) (a p : ℝ)
    (hmax : p ≤ (sphereMeasure d R).real {z | a ≤ max (f z) (f (-z))}) :
    p / 2 ≤ (sphereMeasure d R).real {z | a ≤ f z} := by
  let A : Set (Space d) := {z | a ≤ f z}
  have hA : MeasurableSet A := measurableSet_le measurable_const hf
  have heq : {z | a ≤ max (f z) (f (-z))} = A ∪ (fun x => -x) ⁻¹' A := by
    ext x
    simp only [Set.mem_ofPred_eq, le_max_iff, Set.mem_union, Set.mem_preimage, A]
  rw [heq] at hmax
  have hsym : (sphereMeasure d R).real ((fun x => -x) ⁻¹' A) =
      (sphereMeasure d R).real A := by
    unfold Measure.real
    rw [sphereMeasure_neg_preimage R hA]
  have hbound := measureReal_union_le (μ := sphereMeasure d R) A ((fun x => -x) ⁻¹' A)
  rw [hsym] at hbound
  dsimp [A] at hbound
  dsimp [A] at hmax
  linarith

end LG2021

end
end

/- LG2021GaussianSphereEvents -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

private theorem gaussian_inner_sq_integrable {d : ℕ} (q : Space d) :
    Integrable (fun x => (inner ℝ q x) ^ 2) (gaussian d) := by
  exact (IsGaussian.memLp_dual (gaussian d) (innerSL ℝ q) 2 (by norm_num)).integrable_sq

private theorem gaussian_inner_fourth_integrable {d : ℕ} (q : Space d) :
    Integrable (fun x => (inner ℝ q x) ^ 4) (gaussian d) := by
  have h := (IsGaussian.memLp_dual (gaussian d) (innerSL ℝ q) 4
    (by norm_num)).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have heq : (fun x : Space d => ‖innerSL ℝ q x‖ ^ 4) =
      fun x => (inner ℝ q x) ^ 4 := by
    funext x
    simp only [innerSL_apply_apply, Real.norm_eq_abs,
      show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
  simpa only [heq] using h

private theorem gaussian_weighted_projection_first_moment {ι : Type*} [Fintype ι] {d : ℕ}
    (a : ι → ℝ) (v : ι → Space d) (hv : ∀ i, ‖v i‖ = 1) :
    (∫ x, ∑ i, a i * (inner ℝ (v i) x) ^ 2 ∂gaussian d) = ∑ i, a i := by
  rw [integral_finsetSum _ (fun i _ => (gaussian_inner_sq_integrable (v i)).const_mul (a i))]
  simp only [integral_const_mul, gaussian_inner_second_moment, hv, one_pow, mul_one]

private theorem gaussian_weighted_projection_second_moment {ι : Type*} [Fintype ι] {d : ℕ}
    (a : ι → ℝ) (v : ι → Space d) (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, ‖v i‖ = 1) :
    Integrable (fun x => (∑ i, a i * (inner ℝ (v i) x) ^ 2) ^ 2) (gaussian d) ∧
      (∫ x, (∑ i, a i * (inner ℝ (v i) x) ^ 2) ^ 2 ∂gaussian d) ≤
        3 * (∑ i, a i) ^ 2 := by
  have hT : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  have hpoint (x : Space d) :
      (∑ i, a i * (inner ℝ (v i) x) ^ 2) ^ 2 ≤
        (∑ i, a i) * ∑ i, a i * (inner ℝ (v i) x) ^ 4 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => ha i) (fun i _ => mul_nonneg (ha i) (by positivity))
    intro i _
    ring_nf
    exact le_rfl
  have hmajorant : Integrable
      (fun x => (∑ i, a i) * ∑ i, a i * (inner ℝ (v i) x) ^ 4) (gaussian d) :=
    (integrable_finsetSum Finset.univ (fun i _ =>
      (gaussian_inner_fourth_integrable (v i)).const_mul (a i))).const_mul _
  have hint : Integrable (fun x => (∑ i, a i * (inner ℝ (v i) x) ^ 2) ^ 2)
      (gaussian d) :=
    hmajorant.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint x)
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x, (∑ i, a i) * ∑ i, a i * (inner ℝ (v i) x) ^ 4 ∂gaussian d :=
      integral_mono hint hmajorant hpoint
    _ = _ := by
      rw [integral_const_mul,
        integral_finsetSum _ (fun i _ => (gaussian_inner_fourth_integrable (v i)).const_mul (a i))]
      simp only [integral_const_mul, gaussian_inner_fourth_moment, hv, one_pow,
        mul_one, ← Finset.sum_mul]
      ring

private theorem gaussian_norm_sq_markov (d : ℕ) (c : ℝ) :
    c * (gaussian d).real {x | c ≤ ‖x‖ ^ 2} ≤ d := by
  simpa only [gaussian_norm_second_moment] using
    mul_meas_ge_le_integral_of_nonneg (μ := gaussian d)
      (Filter.Eventually.of_forall fun x => sq_nonneg ‖x‖)
      (gaussian_norm_sq_integrable d) c

private theorem quadraticForm_eq_inner {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (z : Space d) :
    quadraticForm M z = inner ℝ z (M.toEuclideanLin z) := by
  simp [quadraticForm, PiLp.inner_apply, Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm,
    mul_left_comm]

private theorem quadraticForm_eigen_sum {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.IsHermitian) (z : Space d) :
    quadraticForm M z =
      ∑ i, hM.eigenvalues i * (inner ℝ (hM.eigenvectorBasis i) z) ^ 2 := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  have heigen (i : Fin d) : M.toEuclideanLin (hM.eigenvectorBasis i) =
      hM.eigenvalues i • hM.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    change (Matrix.mulVec M ⇑(hM.eigenvectorBasis i)) j = _
    rw [hM.mulVec_eigenvectorBasis]
    rfl
  have hinner (i : Fin d) :
      inner ℝ (hM.eigenvectorBasis i) (M.toEuclideanLin z) =
        hM.eigenvalues i * inner ℝ (hM.eigenvectorBasis i) z := by
    rw [← hs (hM.eigenvectorBasis i) z, heigen i, real_inner_smul_left]
  rw [quadraticForm_eq_inner, ← hM.eigenvectorBasis.sum_inner_mul_inner z (M.toEuclideanLin z)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hinner i, real_inner_comm z (hM.eigenvectorBasis i)]
  ring

private theorem quadraticForm_nonneg {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) (z : Space d) : 0 ≤ quadraticForm M z := by
  rw [quadraticForm_eigen_sum hM.isHermitian]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hM.eigenvalues_nonneg i) (sq_nonneg _)

private theorem quadraticForm_le_trace_mul_norm_sq {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef) (z : Space d) :
    quadraticForm M z ≤ Matrix.trace M * ‖z‖ ^ 2 := by
  rw [quadraticForm_eigen_sum hM.isHermitian]
  have htrace : Matrix.trace M = ∑ i, hM.isHermitian.eigenvalues i := by
    simpa using hM.isHermitian.trace_eq_sum_eigenvalues
  rw [htrace, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hM.eigenvalues_nonneg i)
  have hi := abs_real_inner_le_norm (hM.isHermitian.eigenvectorBasis i) z
  rw [hM.isHermitian.eigenvectorBasis.orthonormal.1 i, one_mul] at hi
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (inner ℝ (hM.isHermitian.eigenvectorBasis i) z))
      (norm_nonneg z)).2 hi

private theorem gaussian_quadratic_first_moment {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) :
    (∫ x, quadraticForm M x ∂gaussian d) = Matrix.trace M := by
  have h := gaussian_weighted_projection_first_moment hM.isHermitian.eigenvalues
    hM.isHermitian.eigenvectorBasis hM.isHermitian.eigenvectorBasis.orthonormal.1
  have htrace : Matrix.trace M = ∑ i, hM.isHermitian.eigenvalues i := by
    simpa using hM.isHermitian.trace_eq_sum_eigenvalues
  simpa only [← quadraticForm_eigen_sum hM.isHermitian, ← htrace] using h

private theorem gaussian_quadratic_second_moment {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) :
    Integrable (fun x => quadraticForm M x ^ 2) (gaussian d) ∧
      (∫ x, quadraticForm M x ^ 2 ∂gaussian d) ≤ 3 * Matrix.trace M ^ 2 := by
  have h := gaussian_weighted_projection_second_moment hM.isHermitian.eigenvalues
    hM.isHermitian.eigenvectorBasis hM.eigenvalues_nonneg
    hM.isHermitian.eigenvectorBasis.orthonormal.1
  have htrace : Matrix.trace M = ∑ i, hM.isHermitian.eigenvalues i := by
    simpa using hM.isHermitian.trace_eq_sum_eigenvalues
  simpa only [← quadraticForm_eigen_sum hM.isHermitian, ← htrace] using h

private theorem real_paley_quarter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Q : Ω → ℝ) (hQ : Measurable Q)
    (hQn : ∀ x, 0 ≤ Q x) (hi : Integrable Q μ)
    (hi2 : Integrable (fun x => Q x ^ 2) μ)
    (hsecond : (∫ x, Q x ^ 2 ∂μ) ≤ 3 * (∫ x, Q x ∂μ) ^ 2) :
    (3 / 16 : ℝ) ≤ μ.real {x | (∫ y, Q y ∂μ) / 4 ≤ Q x} := by
  have hIn : 0 ≤ ∫ x, Q x ∂μ := integral_nonneg hQn
  have hJn : 0 ≤ ∫ x, Q x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg (Q x))
  by_cases hzero : (∫ x, Q x ∂μ) = 0
  · rw [hzero]
    have hevent : {x | (0 : ℝ) / 4 ≤ Q x} = Set.univ := by
      ext x
      simp [hQn x]
    rw [hevent]
    norm_num
  have hIpos : 0 < ∫ x, Q x ∂μ := lt_of_le_of_ne hIn (Ne.symm hzero)
  have hI : (∫⁻ x, ENNReal.ofReal (Q x) ∂μ) = ENNReal.ofReal (∫ x, Q x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hQn)).symm
  have hJ : (∫⁻ x, ENNReal.ofReal (Q x) ^ 2 ∂μ) =
      ENNReal.ofReal (∫ x, Q x ^ 2 ∂μ) := by
    simp_rw [← ENNReal.ofReal_pow (hQn _) 2]
    exact (ofReal_integral_eq_lintegral_ofReal hi2
      (Filter.Eventually.of_forall fun x => sq_nonneg (Q x))).symm
  have h := MeasureTheory.lintegral_sq_mul_measure_ge_le μ hQ.ennreal_ofReal
    (by rw [hI]; exact ENNReal.ofReal_ne_top) (1 / 4 : ℝ≥0)
  rw [hI, hJ] at h
  have hevent : {x | ((1 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (∫ y, Q y ∂μ) ≤
      ENNReal.ofReal (Q x)} = {x | (∫ y, Q y ∂μ) / 4 ≤ Q x} := by
    ext x
    have hmul : ((1 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (∫ y, Q y ∂μ) =
        ENNReal.ofReal ((∫ y, Q y ∂μ) / 4) := by
      rw [show ((1 / 4 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 / 4 : ℝ) by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
            norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      congr 1
      ring
    rw [hmul]
    exact ENNReal.ofReal_le_ofReal_iff (hQn x)
  rw [hevent] at h
  have hreal := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2 h
  have hreal' : (9 / 16 : ℝ) * (∫ x, Q x ∂μ) ^ 2 ≤
      (∫ x, Q x ^ 2 ∂μ) * μ.real {x | (∫ y, Q y ∂μ) / 4 ≤ Q x} := by
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hIn,
      ENNReal.toReal_ofReal hJn, measureReal_def] at hreal
    exact hreal
  have hupper := mul_le_mul_of_nonneg_right hsecond
    (measureReal_nonneg (μ := μ) (s := {x | (∫ y, Q y ∂μ) / 4 ≤ Q x}))
  have hbound := hreal'.trans hupper
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hIpos)).1
  nlinarith [hbound]

private theorem gaussian_quadratic_integrable {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosSemidef) : Integrable (quadraticForm M) (gaussian d) := by
  have h := integrable_finsetSum Finset.univ (fun i _ =>
    (gaussian_inner_sq_integrable (hM.isHermitian.eigenvectorBasis i)).const_mul
      (hM.isHermitian.eigenvalues i))
  simpa only [← quadraticForm_eigen_sum hM.isHermitian] using h

private theorem gaussian_quadratic_quarter_probability {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef) :
    (3 / 16 : ℝ) ≤ (gaussian d).real {x | Matrix.trace M / 4 ≤ quadraticForm M x} := by
  have h2 := gaussian_quadratic_second_moment hM
  have h := real_paley_quarter (gaussian d) (quadraticForm M)
    (by unfold quadraticForm; fun_prop) (quadraticForm_nonneg hM)
    (gaussian_quadratic_integrable hM) h2.1
    (by simpa only [gaussian_quadratic_first_moment hM] using h2.2)
  simpa only [gaussian_quadratic_first_moment hM] using h

private theorem real_probability_diff_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A B : Set Ω) :
    μ.real A - μ.real B ≤ μ.real (A \ B) := by
  have hsub : A ⊆ (A \ B) ∪ B := by
    intro x hx
    by_cases hb : x ∈ B
    · exact Or.inr hb
    · exact Or.inl ⟨hx, hb⟩
  have h := (measureReal_mono (μ := μ) hsub).trans
    (measureReal_union_le (μ := μ) (A \ B) B)
  linarith

private theorem quadraticForm_smul {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (x : Space d) : quadraticForm M (c • x) = c ^ 2 * quadraticForm M x := by
  unfold quadraticForm
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem sphere_quadratic_large {d : ℕ} (hd : 0 < d)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef) (R : ℝ) :
    (1 / 8 : ℝ) ≤ (sphereMeasure d R).real
      {z | R ^ 2 * Matrix.trace M / (64 * (d : ℝ)) ≤ quadraticForm M z} := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hTn : 0 ≤ Matrix.trace M := by
    have ht : Matrix.trace M = ∑ i, hM.isHermitian.eigenvalues i := by
      simpa using hM.isHermitian.trace_eq_sum_eigenvalues
    rw [ht]
    exact Finset.sum_nonneg fun i _ => hM.eigenvalues_nonneg i
  by_cases hTzero : Matrix.trace M = 0
  · have hevent : {z : Space d | R ^ 2 * Matrix.trace M / (64 * (d : ℝ)) ≤
        quadraticForm M z} = Set.univ := by
      ext z
      simp only [hTzero, mul_zero, zero_div, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact quadraticForm_nonneg hM z
    rw [hevent]
    norm_num
  have hTpos : 0 < Matrix.trace M := lt_of_le_of_ne hTn (Ne.symm hTzero)
  let A : Set (Space d) := {x | Matrix.trace M / 4 ≤ quadraticForm M x}
  let B : Set (Space d) := {x | 16 * (d : ℝ) ≤ ‖x‖ ^ 2}
  have hAprob : (3 / 16 : ℝ) ≤ (gaussian d).real A :=
    gaussian_quadratic_quarter_probability hM
  have hBprob : (gaussian d).real B ≤ 1 / 16 := by
    have hm := gaussian_norm_sq_markov d (16 * (d : ℝ))
    change (16 * (d : ℝ)) * (gaussian d).real B ≤ d at hm
    apply (mul_le_mul_iff_right₀ hdpos).1
    nlinarith [hm]
  have hsub : A \ B ⊆ (fun x : Space d => (R / ‖x‖) • x) ⁻¹'
      {z | R ^ 2 * Matrix.trace M / (64 * (d : ℝ)) ≤ quadraticForm M z} := by
    rintro x ⟨hxA, hxB⟩
    have hqx : Matrix.trace M / 4 ≤ quadraticForm M x := hxA
    have hnorm : ‖x‖ ^ 2 ≤ 16 * (d : ℝ) := (lt_of_not_ge hxB).le
    have hxne : x ≠ 0 := by
      intro hx
      simp [hx, quadraticForm] at hqx
      linarith
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hbase : Matrix.trace M * ‖x‖ ^ 2 ≤ quadraticForm M x * (64 * (d : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hnorm hTn
      have h2 := mul_le_mul_of_nonneg_right hqx (show (0 : ℝ) ≤ 64 * (d : ℝ) by positivity)
      nlinarith [h1, h2]
    change R ^ 2 * Matrix.trace M / (64 * (d : ℝ)) ≤
      quadraticForm M ((R / ‖x‖) • x)
    rw [quadraticForm_smul, div_pow, div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 64 * (d : ℝ))
      (sq_pos_of_pos hxnorm)).2
    nlinarith [mul_le_mul_of_nonneg_left hbase (sq_nonneg R)]
  have htarget : MeasurableSet {z : Space d |
      R ^ 2 * Matrix.trace M / (64 * (d : ℝ)) ≤ quadraticForm M z} := by
    apply measurableSet_le measurable_const
    unfold quadraticForm
    fun_prop
  change (1 / 8 : ℝ) ≤ ((gaussian d).map (fun x : Space d => (R / ‖x‖) • x)).real _
  rw [Measure.real, Measure.map_apply (measurable_gaussian_normalize d R) htarget]
  change (1 / 8 : ℝ) ≤ (gaussian d).real _
  have hm := measureReal_mono (μ := gaussian d) hsub
  have hdiff := real_probability_diff_lower (gaussian d) A B
  linarith

private theorem gaussianReal_small_ball :
    (gaussianReal 0 1).real {x : ℝ | |x| ≤ 1 / 128} ≤ 1 / 64 := by
  have hpdf (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
      nlinarith [Real.pi_gt_three, Real.sqrt_nonneg (2 * Real.pi)]
    have hexp : Real.exp (-x ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sq_nonneg x]
    have hr : gaussianPDFReal 0 1 x ≤ 1 := by
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
      have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ hnorm
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul hinv hexp (Real.exp_pos _).le (by norm_num)
        _ = 1 := one_mul 1
    simpa only [gaussianPDF, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  have hset : {x : ℝ | |x| ≤ 1 / 128} = Set.Icc (-1 / 128) (1 / 128) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    norm_num
  rw [hset]
  have hm : gaussianReal 0 1 (Set.Icc (-1 / 128 : ℝ) (1 / 128)) ≤
      volume (Set.Icc (-1 / 128 : ℝ) (1 / 128)) := by
    rw [gaussianReal_apply 0 one_ne_zero]
    calc
      _ ≤ ∫⁻ _ in Set.Icc (-1 / 128 : ℝ) (1 / 128), (1 : ℝ≥0∞) :=
        lintegral_mono hpdf
      _ = _ := by simp
  have hh := ENNReal.toReal_mono (isCompact_Icc.measure_ne_top) hm
  change (gaussianReal 0 1).real _ ≤ volume.real _ at hh
  rw [Real.volume_real_Icc_of_le (by norm_num)] at hh
  norm_num at hh ⊢
  exact hh

private theorem gaussian_linear_small_ball {d : ℕ} {q : Space d} (hq : q ≠ 0) :
    (gaussian d).real {x | |inner ℝ q x| ≤ ‖q‖ / 128} ≤ 1 / 64 := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hpre : (fun x : ℝ => ‖q‖ * x) ⁻¹' {t | |t| ≤ ‖q‖ / 128} =
      {x : ℝ | |x| ≤ 1 / 128} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, abs_mul, abs_norm]
    rw [div_eq_mul_inv, show (1 / 128 : ℝ) = 128⁻¹ by norm_num,
      mul_le_mul_iff_right₀ hqn]
  have heq := congrArg (fun μ : Measure ℝ => μ.real {t | |t| ≤ ‖q‖ / 128})
    (gaussian_inner_map q)
  have hs : MeasurableSet {t : ℝ | |t| ≤ ‖q‖ / 128} :=
    measurableSet_le (by fun_prop) measurable_const
  simp only [Measure.real] at heq
  rw [Measure.map_apply (by fun_prop : Measurable (fun x : Space d => inner ℝ q x)) hs,
    Measure.map_apply (by fun_prop : Measurable (fun x : ℝ => ‖q‖ * x)) hs] at heq
  rw [hpre] at heq
  change (gaussian d).real {x | |inner ℝ q x| ≤ ‖q‖ / 128} =
    (gaussianReal 0 1).real {x | |x| ≤ 1 / 128} at heq
  rw [heq]
  exact gaussianReal_small_ball

private theorem sphere_linear_large {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (q : Space d) :
    (23 / 24 : ℝ) ≤ (sphereMeasure d R).real
      {z | R * ‖q‖ / (1024 * Real.sqrt (d : ℝ)) ≤ |inner ℝ q z|} := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hspos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
  have hsq : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdpos.le
  by_cases hq : q = 0
  · subst q
    have hevent : {z : Space d | R * ‖(0 : Space d)‖ /
        (1024 * Real.sqrt (d : ℝ)) ≤ |inner ℝ (0 : Space d) z|} = Set.univ := by
      ext z
      simp
    rw [hevent]
    norm_num
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let A : Set (Space d) := {x | ‖q‖ / 128 < |inner ℝ q x|}
  let B : Set (Space d) := {x | 48 * (d : ℝ) ≤ ‖x‖ ^ 2}
  have hAprob : (63 / 64 : ℝ) ≤ (gaussian d).real A := by
    have hsmall := gaussian_linear_small_ball hq
    have hcomp : A = {x : Space d | |inner ℝ q x| ≤ ‖q‖ / 128}ᶜ := by
      ext x
      simp [A, not_le]
    rw [hcomp, measureReal_compl (measurableSet_le (by fun_prop) measurable_const)]
    norm_num
    linarith
  have hBprob : (gaussian d).real B ≤ 1 / 48 := by
    have hm := gaussian_norm_sq_markov d (48 * (d : ℝ))
    change (48 * (d : ℝ)) * (gaussian d).real B ≤ d at hm
    apply (mul_le_mul_iff_right₀ hdpos).1
    nlinarith [hm]
  have hsub : A \ B ⊆ (fun x : Space d => (R / ‖x‖) • x) ⁻¹'
      {z | R * ‖q‖ / (1024 * Real.sqrt (d : ℝ)) ≤ |inner ℝ q z|} := by
    rintro x ⟨hxA, hxB⟩
    have hax : ‖q‖ / 128 ≤ |inner ℝ q x| := hxA.le
    have hnx : ‖x‖ ^ 2 < 48 * (d : ℝ) := lt_of_not_ge hxB
    have hxne : x ≠ 0 := by
      intro hx
      simp [hx] at hax
      linarith
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
    have hn : ‖x‖ ≤ 8 * Real.sqrt (d : ℝ) := by
      nlinarith [norm_nonneg x]
    have hbase : ‖q‖ * ‖x‖ ≤ |inner ℝ q x| * (1024 * Real.sqrt (d : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hn (norm_nonneg q)
      have h2 := mul_le_mul_of_nonneg_right hax
        (show (0 : ℝ) ≤ 1024 * Real.sqrt (d : ℝ) by positivity)
      nlinarith [h1, h2]
    change R * ‖q‖ / (1024 * Real.sqrt (d : ℝ)) ≤
      |inner ℝ q ((R / ‖x‖) • x)|
    rw [real_inner_smul_right, abs_mul, abs_of_pos (div_pos hR hxnorm)]
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * Real.sqrt (d : ℝ))
      hxnorm).2
    nlinarith [mul_le_mul_of_nonneg_left hbase hR.le]
  have htarget : MeasurableSet {z : Space d |
      R * ‖q‖ / (1024 * Real.sqrt (d : ℝ)) ≤ |inner ℝ q z|} :=
    measurableSet_le measurable_const (by fun_prop)
  change (23 / 24 : ℝ) ≤ ((gaussian d).map (fun x : Space d => (R / ‖x‖) • x)).real _
  rw [Measure.real, Measure.map_apply (measurable_gaussian_normalize d R) htarget]
  change (23 / 24 : ℝ) ≤ (gaussian d).real _
  have hm := measureReal_mono (μ := gaussian d) hsub
  have hdiff := real_probability_diff_lower (gaussian d) A B
  linarith

end LG2021

end
end

/- HessianComparison -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem second_fderiv_quadratic_continuous {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (v : Space d) :
    Continuous (fun x => fderiv ℝ (fderiv ℝ f) x v v) :=
  (((hs.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
    continuous_const).clm_apply continuous_const

private theorem norm_second_fderiv_quadratic_le {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hg : LipschitzWith J (fderiv ℝ f)) (x v : Space d) :
    ‖fderiv ℝ (fderiv ℝ f) x v v‖ ≤ (J : ℝ)*‖v‖^2 := by
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x v‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖*‖v‖)*‖v‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((J : ℝ)*‖v‖)*‖v‖ := by
      gcongr
      exact norm_fderiv_le_of_lipschitz ℝ hg
    _ = _ := by ring

private theorem second_fderiv_quadratic_le_laplacian {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : ContDiff ℝ 2 f) (x v : Space d) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ laplacian f x * ‖v‖^2 := by
  rw [← hessianMatrix_quadraticForm hs]
  exact quadraticForm_le_trace_mul_norm_sq (hessianMatrix_posSemidef hc hs x) v

private theorem gaussian_second_fderiv_quadratic_tail_le {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    (hmin : ∀ x, f 0 ≤ f x) {B delta : ℝ} (hB : 0 ≤ B)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta) (v : Space d) :
    (∫ x in {x : Space d | B < ‖x‖}, fderiv ℝ (fderiv ℝ f) x v v ∂gaussian d) ≤
      ((K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖v‖^2 := by
  have hF := gaussian_integrable_bounded (second_fderiv_quadratic_continuous hs v).aestronglyMeasurable
    (fun x => norm_second_fderiv_quadratic_le hg x v)
  have hL := gaussian_integrable_bounded (laplacian_continuous hs).aestronglyMeasurable
    (norm_laplacian_le hg)
  calc
    _ ≤ ∫ x in {x : Space d | B < ‖x‖}, laplacian f x * ‖v‖^2 ∂gaussian d :=
      integral_mono hF.integrableOn (hL.mul_const _).integrableOn
        (fun x => second_fderiv_quadratic_le_laplacian hc hs x v)
    _ = (∫ x in {x : Space d | B < ‖x‖}, laplacian f x ∂gaussian d)*‖v‖^2 :=
      integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (gaussian_laplacian_tail_le_sqrt hf hc hs hg hmin hB htail) (sq_nonneg _)

private theorem gaussianMollify_symmetric_hessian_lower {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    (hmin : ∀ x, f 0 ≤ f x) {a B c t delta : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hcvar : (1-a^2)*B^2/(2*a^2) ≤ c)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (b v : Space d) (ht : ‖b‖^2/(2*a^2) ≤ t) :
    Real.exp (-(c+t)) * (quadraticForm (curvatureMatrix f) v -
      ((K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖v‖^2) ≤
      (fderiv ℝ (fderiv ℝ (gaussianMollify a f)) b v v +
        fderiv ℝ (fderiv ℝ (gaussianMollify a f)) (-b) v v)/2 := by
  let F : Space d → ℝ := fun x => fderiv ℝ (fderiv ℝ f) x v v
  have hF := gaussian_integrable_bounded (second_fderiv_quadratic_continuous hs v).aestronglyMeasurable
    (fun x => norm_second_fderiv_quadratic_le hg x v)
  have hcomp : {x : Space d | ‖x‖ ≤ B}ᶜ = {x : Space d | B < ‖x‖} := by
    ext x
    simp
  have hsplit := integral_add_compl
    (measurableSet_le measurable_norm (measurable_const : Measurable (fun _ : Space d => B))) hF
  rw [hcomp, ← curvatureMatrix_quadraticForm hf hs hg] at hsplit
  have htailQ := gaussian_second_fderiv_quadratic_tail_le hf hc hs hg hmin hB htail v
  have hinside : quadraticForm (curvatureMatrix f) v -
      ((K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖v‖^2 ≤
      ∫ x in {x : Space d | ‖x‖ ≤ B}, F x ∂gaussian d := by
    dsimp only [F]
    linarith
  have hcompare := gaussian_affine_symmetric_truncated_lower ha ha1 hB hcvar b ht
    (second_fderiv_quadratic_continuous hs v).measurable
    (fun x => convex_second_fderiv_nonneg hc hs x v)
    (fun x => norm_second_fderiv_quadratic_le hg x v)
  have h := (mul_le_mul_of_nonneg_left hinside (Real.exp_pos _).le).trans hcompare
  rw [gaussianMollify_second_fderiv_apply hf hs hg ha,
    gaussianMollify_second_fderiv_apply hf hs hg ha]
  simpa only [F, add_comm b, add_comm (-b), sub_eq_add_neg] using h

end LG2021

end
end

/- Taylor -/
section

noncomputable section
namespace LG2021

private theorem hasDerivAt_line {d : ℕ} {F : Space d → ℝ}
    (hF : Differentiable ℝ F) (v : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (s • v)) (fderiv ℝ F (t • v) v) t := by
  simpa only [Function.comp_def, id_eq, one_smul] using
    (hF (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v)

private theorem deriv_line {d : ℕ} {F : Space d → ℝ}
    (hF : Differentiable ℝ F) (v : Space d) (t : ℝ) :
    deriv (fun s : ℝ => F (s • v)) t = fderiv ℝ F (t • v) v :=
  (hasDerivAt_line hF v t).deriv

private theorem second_deriv_line {d : ℕ} {F : Space d → ℝ}
    (hF : ContDiff ℝ 2 F) (v : Space d) (t : ℝ) :
    deriv (deriv (fun s : ℝ => F (s • v))) t =
      fderiv ℝ (fderiv ℝ F) (t • v) v v := by
  have hfirst : deriv (fun s : ℝ => F (s • v)) = fun s => fderiv ℝ F (s • v) v := by
    funext s
    exact deriv_line (hF.differentiable (by norm_num)) v s
  rw [hfirst]
  have hD := (((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (t • v)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const v))
  have h := hD.clm_apply (hasDerivAt_const t v)
  simpa using h.deriv

private theorem second_derivative_lower_secant {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (c : ℝ) (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1, c ≤ deriv (deriv F) t) :
    c/2 ≤ F 1-F 0-deriv F 0 := by
  let G : ℝ → ℝ := fun t => F t-(c/2)*t^2
  have hG : ContDiff ℝ 2 G := hF.sub (contDiff_const.mul (contDiff_id.pow 2))
  have hdF := hF.differentiable (by norm_num)
  have hdDF := hF.differentiable_deriv_two
  have hdG : ∀ t, HasDerivAt G (deriv F t-c*t) t := by
    intro t
    have h := (hdF t).hasDerivAt.sub (((hasDerivAt_id t).pow 2).const_mul (c/2))
    simp only [id_eq, Pi.pow_apply] at h
    convert! h using 1 <;> ring
  have heq : deriv G = fun t => deriv F t-c*t := funext (fun t => (hdG t).deriv)
  have hddG (t : ℝ) : deriv (deriv G) t = deriv (deriv F) t-c := by
    rw [heq]
    have h := (hdDF t).hasDerivAt.sub ((hasDerivAt_id t).const_mul c)
    change HasDerivAt (fun y => deriv F y-c*y) (deriv (deriv F) t-c*1) t at h
    simpa only [mul_one] using h.deriv
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) G := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc 0 1)
      (hG.differentiable (by norm_num)).differentiableOn
      hG.differentiable_deriv_two.differentiableOn
    intro t ht
    change 0 ≤ deriv (deriv G) t
    rw [hddG]
    exact sub_nonneg.mpr (hc t ht)
  have h := hconv.le_slope_of_hasDerivAt (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ)<1) (hdG 0)
  simp only [slope_def_field, G, zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_pow,
    mul_zero, sub_zero, mul_one, div_one] at h
  linarith

private theorem symmetric_second_derivative_lower {d : ℕ} {F : Space d → ℝ}
    (hF : ContDiff ℝ 2 F) (v : Space d) (c : ℝ)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      c ≤ fderiv ℝ (fderiv ℝ F) (t • v) v v +
        fderiv ℝ (fderiv ℝ F) (-(t • v)) v v) :
    c/2 ≤ F v+F (-v)-2*F 0 := by
  let G : ℝ → ℝ := fun t => F (t • v)+F (t • (-v))
  have hplus : ContDiff ℝ 2 (fun t : ℝ => F (t • v)) :=
    hF.comp (contDiff_id.smul contDiff_const)
  have hminus : ContDiff ℝ 2 (fun t : ℝ => F (t • (-v))) :=
    hF.comp (contDiff_id.smul contDiff_const)
  have hG : ContDiff ℝ 2 G := hplus.add hminus
  have hfirst : deriv G = fun t => deriv (fun s : ℝ => F (s • v)) t+
      deriv (fun s : ℝ => F (s • (-v))) t := by
    funext t
    exact deriv_add (hplus.differentiable (by norm_num) t)
      (hminus.differentiable (by norm_num) t)
  have hsecond (t : ℝ) : deriv (deriv G) t =
      fderiv ℝ (fderiv ℝ F) (t • v) v v +
        fderiv ℝ (fderiv ℝ F) (-(t • v)) v v := by
    rw [hfirst]
    change deriv ((deriv (fun s : ℝ => F (s • v))) + deriv (fun s : ℝ => F (s • (-v)))) t = _
    rw [deriv_add (hplus.differentiable_deriv_two t)
      (hminus.differentiable_deriv_two t), second_deriv_line hF, second_deriv_line hF]
    simp only [smul_neg, map_neg, neg_apply, neg_neg]
  have hzero : deriv G 0 = 0 := by
    rw [hfirst]
    dsimp only
    rw [deriv_line (hF.differentiable (by norm_num)),
      deriv_line (hF.differentiable (by norm_num))]
    simp
  have h := second_derivative_lower_secant hG c (fun t ht => by rw [hsecond]; exact hc t ht)
  rw [hzero] at h
  simpa only [G, one_smul, zero_smul, sub_zero, two_mul] using h

end LG2021

end
end

/- AffineRemainder -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private def affineRemainder {d : ℕ} (f : Space d → ℝ) (x : Space d) : ℝ :=
  f x-f 0-fderiv ℝ f 0 x

private theorem affineRemainder_lipschitz {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : LipschitzWith (2*K) (affineRemainder f) := by
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  have heq : affineRemainder f x-affineRemainder f y =
      (f x-f y)-fderiv ℝ f 0 (x-y) := by unfold affineRemainder; rw [map_sub]; ring
  rw [heq]
  calc
    _ ≤ ‖f x-f y‖+‖fderiv ℝ f 0 (x-y)‖ := norm_sub_le _ _
    _ ≤ (K : ℝ)*‖x-y‖+(K : ℝ)*‖x-y‖ := add_le_add (hf.norm_sub_le x y)
      (((fderiv ℝ f 0).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _)))
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring

private theorem affineRemainder_convex {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) : ConvexOn ℝ Set.univ (affineRemainder f) := by
  have h := (hc.add_const (-f 0)).sub ((fderiv ℝ f 0).toLinearMap.concaveOn convex_univ)
  have heq : affineRemainder f = (f + fun _ => -f 0) - (fun x => fderiv ℝ f 0 x) := by
    funext x
    simp only [affineRemainder, Pi.sub_apply, Pi.add_apply]
    ring
  rw [heq]
  exact h

private theorem affineRemainder_contDiff {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) : ContDiff ℝ 2 (affineRemainder f) :=
  (hs.sub contDiff_const).sub (fderiv ℝ f 0).contDiff

private theorem affineRemainder_fderiv {d : ℕ} {f : Space d → ℝ}
    (hs : Differentiable ℝ f) (x : Space d) :
    fderiv ℝ (affineRemainder f) x = fderiv ℝ f x-fderiv ℝ f 0 := by
  exact (((hs x).hasFDerivAt.sub_const (f 0)).sub (fderiv ℝ f 0).hasFDerivAt).fderiv

private theorem affineRemainder_fderiv_lipschitz {d : ℕ} {f : Space d → ℝ} {J : NNReal}
    (hs : Differentiable ℝ f) (hg : LipschitzWith J (fderiv ℝ f)) :
    LipschitzWith J (fderiv ℝ (affineRemainder f)) := by
  have heq : fderiv ℝ (affineRemainder f) = fun x => fderiv ℝ f x-fderiv ℝ f 0 :=
    funext (affineRemainder_fderiv hs)
  rw [heq]
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  simpa only [sub_sub_sub_cancel_right] using hg.norm_sub_le x y

private theorem affineRemainder_second_fderiv {d : ℕ} {f : Space d → ℝ}
    (hs : ContDiff ℝ 2 f) (x : Space d) :
    fderiv ℝ (fderiv ℝ (affineRemainder f)) x = fderiv ℝ (fderiv ℝ f) x := by
  have heq : fderiv ℝ (affineRemainder f) = fun y => fderiv ℝ f y-fderiv ℝ f 0 :=
    funext (affineRemainder_fderiv (hs.differentiable (by norm_num)))
  rw [heq]
  exact ((((hs.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt).sub_const _).fderiv

private theorem affineRemainder_min_zero {d : ℕ} {f : Space d → ℝ}
    (hc : ConvexOn ℝ Set.univ f) (hs : Differentiable ℝ f) (x : Space d) :
    affineRemainder f 0 ≤ affineRemainder f x := by
  have h := convex_remainder_nonneg hc (hs 0).hasFDerivAt x
  simpa only [affineRemainder, sub_self, map_zero, sub_zero] using h

private theorem affineRemainder_curvatureMatrix {d : ℕ} {f : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hs : ContDiff ℝ 2 f)
    (hg : LipschitzWith J (fderiv ℝ f)) :
    curvatureMatrix (affineRemainder f) = curvatureMatrix f := by
  ext i j
  rw [← gaussian_second_partial_identity_lipschitz (affineRemainder_lipschitz hf)
      (affineRemainder_contDiff hs)
      (affineRemainder_fderiv_lipschitz (hs.differentiable (by norm_num)) hg),
    ← gaussian_second_partial_identity_lipschitz hf hs hg]
  congr 1
  funext x
  rw [secondPartialDerivative_eq (affineRemainder_contDiff hs),
    secondPartialDerivative_eq hs, affineRemainder_second_fderiv hs]

private theorem gaussianMean_linear {d : ℕ} (L : Space d →L[ℝ] ℝ) : gaussianMean L = 0 := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := IsGaussian.integrable_fun_id
  unfold gaussianMean
  rw [L.integral_comp_comm hx]
  simp only [gaussian, integral_id_stdGaussian, map_zero]

private theorem surrogate_sub_affine {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0)
    (c : ℝ) (L : Space d →L[ℝ] ℝ) (z : Space d) :
    surrogate lambda (fun x => f x-c-L x) z = surrogate lambda f z-c-L z := by
  have hi := integrable_lipschitz_gaussian hf
  have hL := integrable_lipschitz_gaussian L.lipschitz
  have hia := integrable_lipschitz_gaussian_affine hf (1-lambda) (lambda • z)
  have hLa := integrable_lipschitz_gaussian_affine L.lipschitz (1-lambda) (lambda • z)
  have hmean : gaussianMean (fun x => f x-c-L x) = gaussianMean f-c := by
    unfold gaussianMean
    have hic : Integrable (fun x => f x-c) (gaussian d) := hi.sub (integrable_const c)
    change (∫ x, (f x-c)-L x ∂gaussian d) = _
    rw [integral_sub hic hL,
      integral_sub hi (integrable_const c)]
    change (∫ x, f x ∂gaussian d)-(∫ x, c ∂gaussian d)-gaussianMean L = _
    rw [gaussianMean_linear]
    simp
  have hlin : (∫ x, L ((1-lambda) • x+lambda • z) ∂gaussian d) = lambda*L z := by
    simp only [map_add, map_smul, smul_eq_mul]
    rw [integral_add (hL.const_mul _) (integrable_const _), integral_const_mul]
    change (1-lambda)*gaussianMean L+(∫ x, lambda*L z ∂gaussian d) = _
    rw [gaussianMean_linear]
    simp
  have ha : (∫ x, f ((1-lambda) • x+lambda • z)-c-L ((1-lambda) • x+lambda • z) ∂gaussian d) =
      (∫ x, f ((1-lambda) • x+lambda • z) ∂gaussian d)-c-lambda*L z := by
    have hic : Integrable (fun x => f ((1-lambda) • x+lambda • z)-c) (gaussian d) :=
      hia.sub (integrable_const c)
    rw [integral_sub hic hLa,
      integral_sub hia (integrable_const c), hlin]
    simp
  unfold surrogate
  rw [hmean, ha]
  field_simp
  <;> ring

private theorem surrogate_affineRemainder {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {lambda : ℝ} (hl : lambda ≠ 0) (z : Space d) :
    surrogate lambda (affineRemainder f) z = surrogate lambda f z-f 0-fderiv ℝ f 0 z :=
  surrogate_sub_affine hf hl (f 0) (fderiv ℝ f 0) z

end LG2021

end
end

/- FiniteCurvature -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem gaussianMollify_symmetric_increment {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    (hmin : ∀ x, f 0 ≤ f x) {a B c t delta : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    (hcvar : (1-a^2)*B^2/(2*a^2) ≤ c)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (v : Space d) (ht : ‖v‖^2/(2*a^2) ≤ t) :
    (Real.exp (-(c+t))/2) * (quadraticForm (curvatureMatrix f) v -
      ((K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖v‖^2) ≤
      (gaussianMollify a f v+gaussianMollify a f (-v))/2-gaussianMollify a f 0 := by
  have hsM := gaussianMollify_contDiff_two_of_gradient_lipschitz hf (hs.of_le (by norm_num))
    (gradient_lipschitz_of_fderiv_lipschitz hg) ha
  have h := symmetric_second_derivative_lower hsM v
    (2*Real.exp (-(c+t))*(quadraticForm (curvatureMatrix f) v-
      ((K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖v‖^2)) (fun s hsi => ?_)
  · linarith
  · have hshift : ‖s • v‖^2/(2*a^2) ≤ t := by
      apply le_trans _ ht
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*a^2)
      rw [norm_smul, Real.norm_of_nonneg hsi.1]
      have hs2 : s^2 ≤ 1 := by nlinarith [hsi.1, hsi.2]
      nlinarith [sq_nonneg ‖v‖]
    have hh := gaussianMollify_symmetric_hessian_lower hf hc hs hg hmin
      ha ha1 hB hcvar htail (s • v) v hshift
    linarith

private theorem surrogate_symmetric_increment_of_min_zero {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    (hmin : ∀ x, f 0 ≤ f x) {lambda B c t delta : ℝ}
    (hl : 0 < lambda) (hl1 : lambda < 1) (hB : 0 ≤ B)
    (hcvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ c)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (z : Space d) (ht : ‖lambda • z‖^2/(2*(1-lambda)^2) ≤ t) :
    (lambda/2)*Real.exp (-(c+t))*(quadraticForm (curvatureMatrix f) z-
      ((K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖z‖^2) ≤
      (surrogate lambda f z+surrogate lambda f (-z))/2-surrogate lambda f 0 := by
  have h := gaussianMollify_symmetric_increment hf hc hs hg hmin (sub_pos.mpr hl1)
    (by linarith : 1-lambda ≤ 1) hB hcvar htail (lambda • z) ht
  rw [quadraticForm_smul, norm_smul, Real.norm_of_nonneg hl.le] at h
  have heq : (surrogate lambda f z+surrogate lambda f (-z))/2-surrogate lambda f 0 =
      ((gaussianMollify (1-lambda) f (lambda • z)+
        gaussianMollify (1-lambda) f (-(lambda • z)))/2-gaussianMollify (1-lambda) f 0)/lambda := by
    simp only [surrogate, gaussianMollify, smul_neg, smul_zero, add_zero, zero_add]
    simp_rw [add_comm ((1-lambda) • _)]
    ring
  rw [heq]
  apply (le_div_iff₀ hl).2
  nlinarith

private theorem surrogate_symmetric_increment {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    {lambda B c t delta : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (hB : 0 ≤ B)
    (hcvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ c)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (z : Space d) (ht : ‖lambda • z‖^2/(2*(1-lambda)^2) ≤ t) :
    (lambda/2)*Real.exp (-(c+t))*(quadraticForm (curvatureMatrix f) z-
      (2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖z‖^2) ≤
      (surrogate lambda f z+surrogate lambda f (-z))/2-surrogate lambda f 0 := by
  have h := surrogate_symmetric_increment_of_min_zero (affineRemainder_lipschitz hf)
    (affineRemainder_convex hc) (affineRemainder_contDiff hs)
    (affineRemainder_fderiv_lipschitz (hs.differentiable (by norm_num)) hg)
    (affineRemainder_min_zero hc (hs.differentiable (by norm_num)))
    hl hl1 hB hcvar htail z ht
  rw [affineRemainder_curvatureMatrix hf hs hg] at h
  simp only [surrogate_affineRemainder hf hl.ne', map_neg, map_zero,
    NNReal.coe_mul, NNReal.coe_ofNat] at h
  linarith

private theorem surrogate_zero_ge_value_sub_trace {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    {lambda : ℝ} (hl : 0 < lambda) :
    f 0-Matrix.trace (curvatureMatrix f) ≤ surrogate lambda f 0 := by
  have h := gaussianMean_sub_surrogate_zero_le_radial_derivative hf hc
    (hs.of_le (by norm_num)) hl
  rw [gaussian_radial_derivative_eq_trace hf hs hg] at h
  linarith [gaussianMean_ge_value_zero hf hc]

private theorem surrogate_symmetric_gain {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    {lambda B c t delta : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (hB : 0 ≤ B)
    (hcvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ c)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (z : Space d) (ht : ‖lambda • z‖^2/(2*(1-lambda)^2) ≤ t) :
    (lambda/2)*Real.exp (-(c+t))*(quadraticForm (curvatureMatrix f) z-
      (2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta))*‖z‖^2)-Matrix.trace (curvatureMatrix f) ≤
      (surrogate lambda f z+surrogate lambda f (-z))/2-f 0 := by
  have h1 := surrogate_symmetric_increment hf hc hs hg hl hl1 hB hcvar htail z ht
  have h2 := surrogate_zero_ge_value_sub_trace hf hc hs hg hl
  linarith

end LG2021

end
end

/- Separation -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory

private theorem surrogate_symmetric_linear_gain {d : ℕ} {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    {lambda : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (z : Space d) :
    |inner ℝ (gradient (surrogate lambda f) 0) z|-Matrix.trace (curvatureMatrix f) ≤
      max (surrogate lambda f z-f 0) (surrogate lambda f (-z)-f 0) := by
  have hD := (surrogate_hasFDerivAt hf hl.ne' hl1 (0 : Space d)).differentiableAt.hasFDerivAt
  have hp := convex_supporting_fderiv (surrogate_convex hf hc hl) hD z
  have hm := convex_supporting_fderiv (surrogate_convex hf hc hl) hD (-z)
  have h0 := surrogate_zero_ge_value_sub_trace hf hc hs hg hl
  simp only [sub_zero, map_neg] at hp hm
  have heq : inner ℝ (gradient (surrogate lambda f) 0) z =
      fderiv ℝ (surrogate lambda f) 0 z := by
    rw [← toDual_gradient]
    rfl
  rw [heq]
  by_cases hsign : 0 ≤ fderiv ℝ (surrogate lambda f) 0 z
  · rw [abs_of_nonneg hsign]
    exact (by linarith : _ ≤ surrogate lambda f z-f 0).trans (le_max_left _ _)
  · rw [abs_of_neg (lt_of_not_ge hsign)]
    exact (by linarith : _ ≤ surrogate lambda f (-z)-f 0).trans (le_max_right _ _)

private theorem norm_gaussian_normalize_le {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : Space d) :
    ‖(R/‖x‖) • x‖ ≤ R := by
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR (norm_nonneg x))]
  by_cases hx : ‖x‖ = 0
  · simp only [hx, div_zero, mul_zero]
    exact hR
  · rw [div_mul_cancel₀ R hx]

private theorem sphereMeasure_norm_gt_zero {d : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (sphereMeasure d R).real {z | R < ‖z‖} = 0 := by
  unfold sphereMeasure Measure.real
  rw [Measure.map_apply (measurable_gaussian_normalize d R)
    (measurableSet_lt measurable_const measurable_norm)]
  have heq : (fun x : Space d => (R/‖x‖) • x) ⁻¹' {z | R < ‖z‖} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact norm_gaussian_normalize_le hR x
  rw [heq, measure_empty, ENNReal.toReal_zero]

private theorem separation_case_split {A T W e C gap : ℝ} (hC : 1 ≤ C)
    (hT : 0 ≤ T) (he : 0 ≤ e) (hgap : gap ≤ A+T)
    (hcurv : 3*T-e ≤ W) (hlin : 2*A/C-T ≤ W) : gap/C-e ≤ W := by
  have hCpos : 0 < C := by linarith
  have hlin0 : 2*A/C ≤ W+T := by linarith
  have hlin' : 2*A ≤ C*(W+T) := by
    simpa only [mul_comm C] using (div_le_iff₀ hCpos).1 hlin0
  have hcurv' := mul_le_mul_of_nonneg_left hcurv hCpos.le
  have hCT := mul_nonneg (show 0 ≤ 2*C-2 by linarith) hT
  have hCe := mul_nonneg hCpos.le he
  have hh : gap ≤ (W+e)*C := by nlinarith
  have hdiv := (div_le_iff₀ hCpos).2 hh
  linarith

private theorem sphere_joint_quadratic_linear {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef) (q : Space d) :
    (1/12 : ℝ) ≤ (sphereMeasure d R).real
      {z | R^2*Matrix.trace M/(64*(d : ℝ)) ≤ quadraticForm M z ∧
        R*‖q‖/(1024*Real.sqrt (d : ℝ)) ≤ |inner ℝ q z| ∧ ‖z‖ ≤ R} := by
  let A : Set (Space d) := {z | R^2*Matrix.trace M/(64*(d : ℝ)) ≤ quadraticForm M z}
  let B : Set (Space d) := {z | R*‖q‖/(1024*Real.sqrt (d : ℝ)) ≤ |inner ℝ q z|}
  let E : Set (Space d) := {z | R < ‖z‖}
  have hA := sphere_quadratic_large hd hM R
  have hB := sphere_linear_large hd hR q
  have hBm : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  have hBc : (sphereMeasure d R).real Bᶜ = 1-(sphereMeasure d R).real B := by
    rw [measureReal_compl hBm]
    simp
  have hE : (sphereMeasure d R).real E = 0 := sphereMeasure_norm_gt_zero hR.le
  have hdiff := real_probability_diff_lower (sphereMeasure d R) A Bᶜ
  have hdiff2 := real_probability_diff_lower (sphereMeasure d R) (A \ Bᶜ) E
  have heq : (A \ Bᶜ) \ E = {z | R^2*Matrix.trace M/(64*(d : ℝ)) ≤ quadraticForm M z ∧
      R*‖q‖/(1024*Real.sqrt (d : ℝ)) ≤ |inner ℝ q z| ∧ ‖z‖ ≤ R} := by
    ext z
    simp only [A, B, E, Set.mem_diff, Set.mem_compl_iff, Set.mem_setOf_eq, not_not, not_lt, and_assoc]
  rw [hBc] at hdiff
  rw [hE, heq] at hdiff2
  change (1/8 : ℝ) ≤ (sphereMeasure d R).real A at hA
  change (23/24 : ℝ) ≤ (sphereMeasure d R).real B at hB
  linarith

private theorem surrogate_separation_smooth {d : ℕ} (hd : 0 < d) {f : Space d → ℝ}
    {K J : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    (hs : ContDiff ℝ 2 f) (hg : LipschitzWith J (fderiv ℝ f))
    {lambda R B delta eps : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (hR : 0 < R)
    (hB : 0 ≤ B) (hvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ 1)
    (hshift : (lambda*R)^2/(2*(1-lambda)^2) ≤ 1)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (hgain : 4 ≤ (lambda/2)*Real.exp (-2)*(R^2/(64*(d : ℝ))))
    (herr : ((lambda/2)*Real.exp (-2)*(2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta)))*R^2 ≤
      eps/(4096*(d : ℝ)*Real.sqrt (d : ℝ))) :
    (1/24 : ℝ) ≤ (sphereMeasure d R).real {z |
      (gaussianGap (2*(d : ℝ)*R) f-eps)/(4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate lambda f z-f 0} := by
  let M := curvatureMatrix f
  let q := gradient (surrogate lambda f) 0
  let T := Matrix.trace M
  let A := (2*(d : ℝ)*R)*‖q‖
  let C := 4096*(d : ℝ)*Real.sqrt (d : ℝ)
  let e := ((lambda/2)*Real.exp (-2)*(2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta)))*R^2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : Real.sqrt (d : ℝ)^2 = d := Real.sq_sqrt hdpos.le
  have hspos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
  have hs1 : 1 ≤ Real.sqrt (d : ℝ) := by nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hCpos : 0 < C := by linarith
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hM : M.PosSemidef := curvatureMatrix_posSemidef hf hc hs hg
  have hT : 0 ≤ T := hM.trace_nonneg
  have hqnorm : ‖q‖ = ‖fderiv ℝ (surrogate lambda f) 0‖ := by
    rw [← toDual_gradient]
    exact ((InnerProductSpace.toDual ℝ (Space d)).norm_map q).symm
  have hgap : gaussianGap (2*(d : ℝ)*R) f ≤ A+T := by
    have h := gaussianGap_le_trace_add_surrogate_gradient hf hc hs hg
      (by positivity : 0 ≤ 2*(d : ℝ)*R) hl hl1
    dsimp only [A, T, M]
    rw [hqnorm]
    linarith
  let target := (gaussianGap (2*(d : ℝ)*R) f-eps)/C
  have hpoint (z : Space d)
      (hzQ : R^2*T/(64*(d : ℝ)) ≤ quadraticForm M z)
      (hzL : R*‖q‖/(1024*Real.sqrt (d : ℝ)) ≤ |inner ℝ q z|)
      (hzR : ‖z‖ ≤ R) :
      target ≤ max (surrogate lambda f z-f 0) (surrogate lambda f (-z)-f 0) := by
    let W := max (surrogate lambda f z-f 0) (surrogate lambda f (-z)-f 0)
    have hz2 : ‖z‖^2 ≤ R^2 := by nlinarith [norm_nonneg z]
    have hzs : ‖lambda • z‖^2/(2*(1-lambda)^2) ≤ 1 := by
      apply le_trans _ hshift
      apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2*(1-lambda)^2)
      rw [norm_smul, Real.norm_of_nonneg hl.le]
      nlinarith [sq_nonneg lambda]
    have hgainZ := surrogate_symmetric_gain hf hc hs hg hl hl1 hB hvar htail z hzs
    norm_num only [show (1:ℝ)+1=2 by norm_num] at hgainZ
    have hcoeff : 0 ≤ (lambda/2)*Real.exp (-2) := by positivity
    have hQ := mul_le_mul_of_nonneg_left hzQ hcoeff
    have hgainT := mul_le_mul_of_nonneg_right hgain hT
    have heZ := mul_le_mul_of_nonneg_left hz2
      (show 0 ≤ (lambda/2)*Real.exp (-2)*(2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta)) by positivity)
    have hW1 : surrogate lambda f z-f 0 ≤ W := le_max_left _ _
    have hW2 : surrogate lambda f (-z)-f 0 ≤ W := le_max_right _ _
    have hQT : 4*T ≤ (lambda/2)*Real.exp (-2)*quadraticForm M z := by
      calc
        _ ≤ (lambda/2)*Real.exp (-2)*(R^2/(64*(d : ℝ)))*T := hgainT
        _ = (lambda/2)*Real.exp (-2)*(R^2*T/(64*(d : ℝ))) := by ring
        _ ≤ _ := hQ
    have hcurv : 3*T-e ≤ W := by
      dsimp only [e, T, M] at *
      nlinarith only [hQT, heZ, hgainZ, hW1, hW2]
    have hlinbase := surrogate_symmetric_linear_gain hf hc hs hg hl hl1 z
    have hlinEq : R*‖q‖/(1024*Real.sqrt (d : ℝ)) = 2*A/C := by
      dsimp [A, C]
      field_simp
      <;> ring
    have hlin : 2*A/C-T ≤ W := by
      rw [hlinEq] at hzL
      change |inner ℝ q z|-T ≤ W at hlinbase
      linarith
    have hcase := separation_case_split hC hT he hgap hcurv hlin
    have heps : e ≤ eps/C := herr
    dsimp only [target]
    rw [sub_div]
    linarith
  have hjoint := sphere_joint_quadratic_linear hd hR hM q
  have hmax : (1/12 : ℝ) ≤ (sphereMeasure d R).real
      {z | target ≤ max (surrogate lambda f z-f 0) (surrogate lambda f (-z)-f 0)} := by
    apply hjoint.trans
    apply measureReal_mono (μ := sphereMeasure d R) _ (measure_ne_top _ _)
    rintro z ⟨hzQ,hzL,hzR⟩
    exact hpoint z hzQ hzL hzR
  have hone := sphereMeasure_one_sided_of_max R
    ((surrogate_lipschitz hf hl).continuous.sub continuous_const).measurable target (1/12) hmax
  norm_num only [show (1/12:ℝ)/2=1/24 by norm_num] at hone
  exact hone

end LG2021

end
end

/- Stability -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Filter Topology

/-- Uniform perturbations of the loss perturb its Gaussian mean by at most the same amount. -/
private theorem gaussianMean_stability {d : ℕ} {f g : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {epsilon : ℝ}
    (he : ∀ x, ‖f x - g x‖ ≤ epsilon) : ‖gaussianMean f - gaussianMean g‖ ≤ epsilon := by
  unfold gaussianMean
  rw [← integral_sub (integrable_lipschitz_gaussian hf) (integrable_lipschitz_gaussian hg)]
  simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using
    norm_integral_le_of_norm_le_const (μ := gaussian d) (Filter.Eventually.of_forall he)

/-- Uniform stability of the actual surrogate, with no differentiability assumption. -/
private theorem surrogate_stability {d : ℕ} {f g : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {epsilon lambda : ℝ}
    (he : ∀ x, ‖f x - g x‖ ≤ epsilon) (z : Space d) :
    ‖surrogate lambda f z - surrogate lambda g z‖ ≤ epsilon + 2 * epsilon / |lambda| := by
  let A := gaussianMean f - gaussianMean g
  let B := (∫ x : Space d, f ((1 - lambda) • x + lambda • z) ∂gaussian d) -
    ∫ x : Space d, g ((1 - lambda) • x + lambda • z) ∂gaussian d
  have hA : ‖A‖ ≤ epsilon := gaussianMean_stability hf hg he
  have hB : ‖B‖ ≤ epsilon := by
    dsimp [B]
    rw [← integral_sub (integrable_lipschitz_gaussian_affine hf _ _)
      (integrable_lipschitz_gaussian_affine hg _ _)]
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := gaussian d)
      (Filter.Eventually.of_forall fun x => he ((1 - lambda) • x + lambda • z))
  have heq : surrogate lambda f z - surrogate lambda g z = A + (B - A) / lambda := by
    dsimp [surrogate, A, B]
    ring
  rw [heq]
  calc
    _ ≤ ‖A‖ + ‖(B - A) / lambda‖ := norm_add_le _ _
    _ = ‖A‖ + ‖B - A‖ / |lambda| := by rw [norm_div, Real.norm_eq_abs lambda]
    _ ≤ epsilon + (‖B‖ + ‖A‖) / |lambda| := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ epsilon + 2 * epsilon / |lambda| := by
      gcongr
      linarith

end LG2021

end
end

/- ClosedEvent -/
section

/-! The closed-event limiting step for uniformly approximated surrogate gaps.
This is an internal continuity-from-above adapter to existing measure theory. -/

noncomputable section
namespace LG2021

open MeasureTheory Filter Set
open scoped Topology

private theorem probability_closed_superlevel_of_uniform_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Ω → ℝ} (hF : Measurable F) {Fseq : ℕ → Ω → ℝ}
    (hlim : TendstoUniformly Fseq F atTop) {p : ℝ}
    (hp : ∀ n, p ≤ μ.real {x | 0 ≤ Fseq n x}) :
    p ≤ μ.real {x | 0 ≤ F x} := by
  let A : ℕ → Set Ω := fun n => {x | -(1 / ((n : ℝ) + 1)) ≤ F x}
  have hA : Antitone A := by
    intro m n hmn x hx
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by gcongr
    exact le_trans (neg_le_neg hdiv) hx
  have hAm : ∀ n, MeasurableSet (A n) := fun _ => measurableSet_le measurable_const hF
  have hbound : ∀ n, p ≤ μ.real (A n) := by
    intro n
    have heps : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨k, hk⟩ := (Metric.tendstoUniformly_iff.mp hlim _ heps).exists
    apply (hp k).trans (measureReal_mono ?_)
    intro x hx
    have he := hk x
    rw [Real.dist_eq] at he
    have hlow := (abs_lt.mp he).1
    change -(1 / ((n : ℝ) + 1)) ≤ F x
    change 0 ≤ Fseq k x at hx
    linarith
  have hInter : (⋂ n, A n) = {x | 0 ≤ F x} := by
    ext x
    constructor
    · intro hx
      by_contra hneg
      have hpos : 0 < -F x := by simpa using (lt_of_not_ge hneg)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have hx' := mem_iInter.mp hx n
      change -(1 / ((n : ℝ) + 1)) ≤ F x at hx'
      linarith
    · intro hx
      apply mem_iInter.mpr
      intro n
      change -(1 / ((n : ℝ) + 1)) ≤ F x
      exact le_trans (neg_nonpos.mpr (by positivity)) hx
  have hENN : ENNReal.ofReal p ≤ μ {x | 0 ≤ F x} := by
    rw [← hInter, hA.measure_iInter (fun n => (hAm n).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    apply le_iInf
    intro n
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (A n))).2 (hbound n)
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hENN

private theorem compact_minimum_stability {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    {f g : X → ℝ} (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    {ε : ℝ} (hclose : ∀ x ∈ K, ‖f x - g x‖ ≤ ε) :
    ‖sInf (f '' K) - sInf (g '' K)‖ ≤ ε := by
  obtain ⟨x, hx, hminf⟩ := hK.exists_isMinOn hne hf
  obtain ⟨y, hy, hming⟩ := hK.exists_isMinOn hne hg
  have hleastf : IsLeast (f '' K) (f x) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact hminf hw
  have hleastg : IsLeast (g '' K) (g y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact hming hw
  rw [hleastf.csInf_eq, hleastg.csInf_eq, Real.norm_eq_abs, abs_le]
  have hfx := hclose x hx
  have hgy := hclose y hy
  rw [Real.norm_eq_abs, abs_le] at hfx hgy
  have hxy : f x ≤ f y := hminf hy
  have hyx : g y ≤ g x := hming hx
  constructor <;> linarith

private theorem gaussianGap_stability {d : ℕ} {f g : Space d → ℝ} {K J : NNReal}
    (hf : LipschitzWith K f) (hg : LipschitzWith J g) {ε r : ℝ}
    (hr : 0 ≤ r) (hclose : ∀ x, ‖f x - g x‖ ≤ ε) :
    ‖gaussianGap r f - gaussianGap r g‖ ≤ 2 * ε := by
  have hmin := compact_minimum_stability (isCompact_closedBall (0 : Space d) r)
    ⟨0, by simpa using hr⟩ hf.continuous.continuousOn hg.continuous.continuousOn
    (fun x _ => hclose x)
  have hmean := gaussianMean_stability hf hg hclose
  have he : gaussianGap r f - gaussianGap r g =
      (gaussianMean f - gaussianMean g) -
        (sInf (f '' Metric.closedBall (0 : Space d) r) - sInf (g '' Metric.closedBall 0 r)) := by
    unfold gaussianGap
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end LG2021

end
end

/- StrongSeparation -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology

private theorem gaussianMollify_twice_uniform_error {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (epsilon : ℝ) (x : Space d) :
    ‖gaussianMollify epsilon (gaussianMollify epsilon f) x-f x‖ ≤
      2*(K : ℝ)*|epsilon| *gaussianMean (fun u : Space d => ‖u‖) := by
  have h1 := gaussianMollify_uniform_error (gaussianMollify_lipschitz hf epsilon) epsilon x
  have h2 := gaussianMollify_uniform_error hf epsilon x
  have h3 := norm_add_le
    (gaussianMollify epsilon (gaussianMollify epsilon f) x-gaussianMollify epsilon f x)
    (gaussianMollify epsilon f x-f x)
  rw [sub_add_sub_cancel] at h3
  linarith

/-- A direct replacement for the paper's separation lemma. The loss is genuinely allowed
to be nonsmooth: the proof regularizes it twice, proves the smooth statement, and passes
the probability of the closed superlevel event to the uniform limit. -/
theorem gaussian_surrogate_separation {d : ℕ} (hd : 0 < d) {f : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    {lambda R B delta eps : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (hR : 0 < R)
    (hB : 0 ≤ B) (hvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ 1)
    (hshift : (lambda*R)^2/(2*(1-lambda)^2) ≤ 1)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (hgain : 4 ≤ (lambda/2)*Real.exp (-2)*(R^2/(64*(d : ℝ))))
    (herr : ((lambda/2)*Real.exp (-2)*(2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta)))*R^2 ≤
      eps/(4096*(d : ℝ)*Real.sqrt (d : ℝ))) :
    (1/24 : ℝ) ≤ (sphereMeasure d R).real {z |
      (gaussianGap (2*(d : ℝ)*R) f-eps)/(4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate lambda f z-f 0} := by
  let epsilon : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  let fseq : ℕ → Space d → ℝ := fun n =>
    gaussianMollify (epsilon n) (gaussianMollify (epsilon n) f)
  let C := 4096*(d : ℝ)*Real.sqrt (d : ℝ)
  let r := 2*(d : ℝ)*R
  let F : Space d → ℝ := fun z => surrogate lambda f z-f 0-(gaussianGap r f-eps)/C
  let Fseq : ℕ → Space d → ℝ := fun n z =>
    surrogate lambda (fseq n) z-fseq n 0-(gaussianGap r (fseq n)-eps)/C
  let error : ℕ → ℝ := fun n => 2*(K : ℝ)*epsilon n*gaussianMean (fun u : Space d => ‖u‖)
  have hepsilon (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hfl (n : ℕ) : LipschitzWith K (fseq n) :=
    gaussianMollify_lipschitz (gaussianMollify_lipschitz hf (epsilon n)) (epsilon n)
  have hfc (n : ℕ) : ConvexOn ℝ Set.univ (fseq n) :=
    gaussianMollify_convex (gaussianMollify_lipschitz hf (epsilon n))
      (gaussianMollify_convex hf hc (epsilon n)) (epsilon n)
  have hfs (n : ℕ) : ContDiff ℝ 2 (fseq n) :=
    gaussianMollify_twice_contDiff_two hf (hepsilon n) (hepsilon n)
  have hfd (n : ℕ) := gaussianMollify_fderiv_lipschitz
    (gaussianMollify_lipschitz hf (epsilon n)) (hepsilon n)
  have hclose (n : ℕ) (x : Space d) : ‖fseq n x-f x‖ ≤ error n := by
    simpa only [fseq, error, abs_of_pos (hepsilon n)] using
      gaussianMollify_twice_uniform_error hf (epsilon n) x
  have herror : Tendsto error atTop (𝓝 0) := by
    have hε : Tendsto epsilon atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [error, mul_zero, zero_mul] using
      (hε.const_mul (2*(K : ℝ))).mul_const (gaussianMean (fun u : Space d => ‖u‖))
  have hbound (n : ℕ) (z : Space d) : ‖Fseq n z-F z‖ ≤
      error n+2*error n/|lambda|+error n+2*error n/C := by
    have hsg := surrogate_stability (lambda := lambda) (hfl n) hf (hclose n) z
    have hgap := gaussianGap_stability (hfl n) hf hr (hclose n)
    have heq : Fseq n z-F z =
        ((surrogate lambda (fseq n) z-surrogate lambda f z)-(fseq n 0-f 0))-
          (gaussianGap r (fseq n)-gaussianGap r f)/C := by
      dsimp [Fseq, F]
      ring
    rw [heq]
    calc
      _ ≤ ‖(surrogate lambda (fseq n) z-surrogate lambda f z)-(fseq n 0-f 0)‖+
          ‖(gaussianGap r (fseq n)-gaussianGap r f)/C‖ := norm_sub_le _ _
      _ ≤ (‖surrogate lambda (fseq n) z-surrogate lambda f z‖+‖fseq n 0-f 0‖)+
          ‖gaussianGap r (fseq n)-gaussianGap r f‖/C := by
        rw [norm_div, Real.norm_of_nonneg hCpos.le]
        exact add_le_add
          (norm_sub_le (surrogate lambda (fseq n) z-surrogate lambda f z) (fseq n 0-f 0)) le_rfl
      _ ≤ _ := add_le_add (add_le_add hsg (hclose n 0))
        (div_le_div_of_nonneg_right hgap hCpos.le)
  have hlim : TendstoUniformly Fseq F atTop := by
    apply Metric.tendstoUniformly_iff.2
    intro eta heta
    have hb : Tendsto (fun n => error n+2*error n/|lambda|+error n+2*error n/C)
        atTop (𝓝 0) := by
      simpa only [mul_zero, zero_div, zero_add] using
        (((herror.add ((herror.const_mul 2).div_const |lambda|)).add herror).add
          ((herror.const_mul 2).div_const C))
    filter_upwards [(tendsto_order.1 hb).2 eta heta] with n hn z
    simpa only [dist_eq_norm, norm_sub_rev] using (hbound n z).trans_lt hn
  have hprob (n : ℕ) : (1/24 : ℝ) ≤ (sphereMeasure d R).real {z | 0 ≤ Fseq n z} := by
    have h := surrogate_separation_smooth hd (hfl n) (hfc n) (hfs n) (hfd n)
      hl hl1 hR hB hvar hshift htail hgain herr
    simpa only [Fseq, C, r, sub_nonneg] using h
  have hF : Measurable F := by
    exact (((surrogate_lipschitz hf hl).continuous.sub continuous_const).sub continuous_const).measurable
  have h := probability_closed_superlevel_of_uniform_limit (sphereMeasure d R) hF hlim hprob
  simpa only [F, C, r, sub_nonneg] using h

end LG2021

end
end

open LG2021 MeasureTheory ProbabilityTheory

theorem solution {d : ℕ} (hd : 0 < d) {f : Space d → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f)
    {lambda R B delta eps : ℝ} (hl : 0 < lambda) (hl1 : lambda < 1) (hR : 0 < R)
    (hB : 0 ≤ B) (hvar : (1-(1-lambda)^2)*B^2/(2*(1-lambda)^2) ≤ 1)
    (hshift : (lambda*R)^2/(2*(1-lambda)^2) ≤ 1)
    (htail : (gaussian d).real {x : Space d | B < ‖x‖} ≤ delta)
    (hgain : 4 ≤ (lambda/2)*Real.exp (-2)*(R^2/(64*(d : ℝ))))
    (herr : ((lambda/2)*Real.exp (-2)*(2*(K : ℝ)*Real.sqrt ((d : ℝ)*delta)))*R^2 ≤
      eps/(4096*(d : ℝ)*Real.sqrt (d : ℝ))) :
    (1/24 : ℝ) ≤ (sphereMeasure d R).real {z |
      (gaussianGap (2*(d : ℝ)*R) f-eps)/(4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate lambda f z-f 0} := by
  exact LG2021.gaussian_surrogate_separation hd hf hc hl hl1 hR hB hvar hshift htail hgain herr
