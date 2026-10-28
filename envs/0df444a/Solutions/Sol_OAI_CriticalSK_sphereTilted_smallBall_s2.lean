-- Prove2me | solution 1 for OAI.CriticalSK.sphereTilted_smallBall_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:12:38.902995+00:00
-- url     : https://prove2.me/submissions/f1e15a1b-b0a5-473c-9d9c-2881e63457e1

import Mathlib
import Definitions.Def_OAIQ074C000

section
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

lemma gaussian_square_density (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_square_integral (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have ha : 0 < 1 / 2 - t := by linarith
  have hb : 0 < 1 - 2 * t := by linarith
  apply (mul_left_inj' (Real.sqrt_ne_zero'.mpr hb)).mp
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hb)]
  have he : Real.sqrt (Real.pi / (1 / 2 - t)) * Real.sqrt (1 - 2 * t) =
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / (1 / 2 - t) * (1 - 2 * t) =
      2 * Real.pi by field_simp]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1 / 2 - t)) *
        Real.sqrt (1 - 2 * t) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
          rw [mul_assoc, he]
    _ = 1 := inv_mul_cancel₀ (by positivity)

lemma gaussian_square_integrable (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  apply mgf_pos_iff.mp
  change 0 < ∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1
  rw [gaussian_square_integral t ht]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_SphereGeometry
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
namespace CriticalSK


section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereArea_pos : 0 < sphereArea (ι := ι) := by
  exact ENNReal.toReal_pos ((measure_univ_pos.mpr (Measure.toSphere_ne_zero _)).ne')
    (measure_ne_top _ _)

end


section

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma integral_polar (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ) :
    (∫ x, f x ∂μ) = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ),
      f (p.2.val • p.1.val) ∂μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1)) := by
  calc
    _ = ∫ x : ({(0)}ᶜ : Set E), f x.val ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _) (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            f ((homeomorphUnitSphereProd E).symm p).val)

lemma radial_map_preserving (μ : Measure E) [μ.IsAddHaarMeasure] :
    MeasurePreserving (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => p.2.val • p.1.val)
      (μ.toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1))) μ := by
  have hs : MeasurePreserving (Subtype.val : ({(0)}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    simpa only [restrict_compl_singleton] using
      (measurePreserving_subtype_coe (μa := μ) (measurableSet_singleton (0 : E)).compl)
  exact hs.comp (MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    μ.measurePreserving_homeomorphUnitSphereProd)

end

end

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_SphereSaddle
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
namespace CriticalSK



section

variable {ι : Type*} [Fintype ι]

lemma gaussianPiPDF_nonneg (v : ι → ℝ≥0) (x : ι → ℝ) : 0 ≤ gaussianPiPDF v x := by
  exact Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)

lemma gaussianPiPDF_integrable (v : ι → ℝ≥0) : Integrable (gaussianPiPDF v) :=
  Integrable.fintype_prod (fun i => integrable_gaussianPDFReal 0 (v i))

lemma gaussianPi_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => gaussianReal 0 (v i)) =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianPiPDF v x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (gaussianPiPDF_integrable v).integrableOn
      (Filter.Eventually.of_forall (gaussianPiPDF_nonneg v))]
  change ENNReal.ofReal (∫ x, gaussianPiPDF v x
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  simp only [gaussianPiPDF]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [gaussianReal_of_var_ne_zero _ (hv i), withDensity_apply _ (hs i)]
    exact ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianPDFReal 0 (v i)).integrableOn
      (Filter.Eventually.of_forall (gaussianPDFReal_nonneg 0 (v i)))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg 0 (v i))

lemma gaussianPiPDF_continuous (v : ι → ℝ≥0) : Continuous (gaussianPiPDF v) := by
  unfold gaussianPiPDF gaussianPDFReal
  fun_prop

lemma map_density_of_preserving {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {T : X → Y} (hT : MeasurePreserving T μ ν)
    (w : Y → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun x => w (T x))).map T = ν.withDensity w := by
  ext A hA
  rw [Measure.map_apply hT.measurable hA, withDensity_apply _ (hT.measurable hA),
    withDensity_apply _ hA]
  exact hT.setLIntegral_comp_preimage hA hw

lemma density_toLp (w : (ι → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    ((volume : Measure (ι → ℝ)).withDensity w).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = volume.withDensity
      (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) :=
    hw.comp (WithLp.measurable_ofLp 2 _)
  simpa only [WithLp.ofLp_toLp] using
    map_density_of_preserving (PiLp.volume_preserving_toLp ι)
      (fun x : EuclideanSpace ℝ ι => w (WithLp.ofLp x)) hm

lemma diagonalGaussian_density (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalGaussian v = volume.withDensity
      (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (gaussianPiPDF v (WithLp.ofLp x))) := by
  change (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = _
  rw [gaussianPi_density v hv]
  exact density_toLp _ (gaussianPiPDF_continuous v).measurable.ennreal_ofReal

lemma euclideanGaussianPDF_continuous (v : ι → ℝ≥0) :
    Continuous (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) :=
  (gaussianPiPDF_continuous v).comp (PiLp.continuous_ofLp 2 _)

lemma euclideanGaussianPDF_integrable (v : ι → ℝ≥0) :
    Integrable (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) := by
  exact (PiLp.volume_preserving_ofLp ι).integrable_comp
    (gaussianPiPDF_integrable v).aestronglyMeasurable |>.mpr (gaussianPiPDF_integrable v)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma integral_polar_iterated (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r : Ioi (0 : ℝ), ∫ u : sphere (0 : E) 1,
      f (r.val • u.val) ∂μ.toSphere ∂volumeIoiPow (Module.finrank ℝ E - 1) := by
  rw [integral_polar μ f]
  exact integral_prod_symm _
    ((radial_map_preserving μ).integrable_comp hf.aestronglyMeasurable |>.mpr hf)

omit [Nontrivial E] in
lemma angular_integral_continuous (μ : Measure E) [μ.IsAddHaarMeasure]
    [ProperSpace E] {f : E → ℝ} (hf : Continuous f) (A : Set (sphere (0 : E) 1)) :
    Continuous (fun r : ℝ => ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere.restrict A) := by
  have h : Continuous (Function.uncurry (fun r : ℝ => fun u : sphere (0 : E) 1 =>
      f (r • u.val))) := hf.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := μ.toSphere.restrict A) h
      (isCompact_univ : IsCompact (Set.univ : Set (sphere (0 : E) 1))))

lemma integral_polar_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) *
      ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere := by
  rw [integral_polar_iterated μ hf, Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => (ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1))).toReal •
      ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma normShell_measurable (a b : ℝ) : MeasurableSet (normShell (E := E) a b) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma normShell_radial (a b : ℝ) (r : Ioi (0 : ℝ)) (u : sphere (0 : E) 1) :
    r.val • u.val ∈ normShell a b ↔ r.val ∈ Ioc a b := by
  have hu : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simp only [normShell, Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos r.property.out,
    hu, mul_one, Set.mem_Ioc]

lemma normShell_integral (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) {a b : ℝ} (ha : 0 ≤ a) :
    (∫ x in normShell a b, f x ∂μ) = ∫ r in Ioc a b,
      r ^ (Module.finrank ℝ E - 1) * ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere := by
  rw [← integral_indicator (normShell_measurable a b),
    integral_polar_real μ (hf.indicator (normShell_measurable a b))]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Ioc a b).indicator
        (fun r => r ^ (Module.finrank ℝ E - 1) *
          ∫ u : sphere (0 : E) 1, f (r • u.val) ∂μ.toSphere) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hh (u : sphere (0 : E) 1) := normShell_radial a b ⟨r, hr⟩ u
      by_cases hab : r ∈ Ioc a b
      · simp only [Set.indicator_of_mem hab]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => Set.indicator_of_mem ((hh u).mpr hab) f)
      · simp only [Set.indicator_of_notMem hab]
        have hz : (∫ u : sphere (0 : E) 1,
            (normShell a b).indicator f (r • u.val) ∂μ.toSphere) = 0 := by
          apply integral_eq_zero_of_ae
          exact Filter.Eventually.of_forall (fun u => Set.indicator_of_notMem
            (fun h => hab ((hh u).mp h)) f)
        rw [hz, mul_zero]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have hsub : Ioc a b ⊆ Ioi (0 : ℝ) := fun _ h => lt_of_le_of_lt ha h.1
      rw [Set.inter_eq_right.mpr hsub]

omit [Nontrivial E] in
lemma radialDensity_continuous (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Continuous f) : Continuous (radialDensity μ f) := by
  have h := angular_integral_continuous μ hf Set.univ
  simp only [Measure.restrict_univ] at h
  exact (continuous_id.pow _).mul h

lemma normShell_density (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b) =
      ENNReal.ofReal (∫ r in Ioc a b, radialDensity μ f r) := by
  rw [withDensity_apply _ (normShell_measurable a b),
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hfn),
    normShell_integral μ hf ha]
  rfl

lemma normShell_density_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {a b : ℝ} (ha : 0 ≤ a) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b)).toReal =
      ∫ r in Ioc a b, radialDensity μ f r := by
  rw [normShell_density μ hf hfn ha, ENNReal.toReal_ofReal]
  apply setIntegral_nonneg measurableSet_Ioc
  intro r hr
  exact mul_nonneg (pow_nonneg (le_trans ha hr.1.le) _) (integral_nonneg (fun u => hfn _))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma squareNormShell_measurable (s δ : ℝ) : MeasurableSet (squareNormShell (E := E) s δ) :=
  (measurableSet_lt measurable_const (measurable_norm.pow_const 2)).inter
    (measurableSet_le (measurable_norm.pow_const 2) measurable_const)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma squareNormShell_eq {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    squareNormShell (E := E) s δ = normShell (Real.sqrt s) (Real.sqrt (s+δ)) := by
  ext x
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt (by linarith : 0 ≤ s+δ)
  have h3 := Real.sqrt_nonneg s
  have h4 := Real.sqrt_nonneg (s+δ)
  have h5 := norm_nonneg x
  change (s < ‖x‖^2 ∧ ‖x‖^2 ≤ s+δ) ↔ (Real.sqrt s < ‖x‖ ∧ ‖x‖ ≤ Real.sqrt (s+δ))
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

lemma squareNormShell_density_limit (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Integrable f μ) (hfc : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun δ : ℝ =>
      (μ.withDensity (fun x => ENNReal.ofReal (f x)) (squareNormShell s δ)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (radialDensity μ f (Real.sqrt s) / (2 * Real.sqrt s))) := by
  have hq := radialDensity_continuous μ hfc
  have hd : HasDerivAt (fun t : ℝ => ∫ r in Real.sqrt s..t, radialDensity μ f r)
      (radialDensity μ f (Real.sqrt s)) (Real.sqrt s) :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hd' := hd.comp s (Real.hasDerivAt_sqrt hs.ne')
  have hh := hd'.tendsto_slope_zero_right
  simp only [Function.comp_def, mul_one_div] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  rw [squareNormShell_eq hs.le hδ0.le,
    normShell_density_real μ hf hfn (Real.sqrt_nonneg _), intervalIntegral.integral_same,
    sub_zero, smul_eq_mul, intervalIntegral.integral_of_le (Real.sqrt_le_sqrt (by linarith))]
  exact mul_comm _ _

end

section

lemma splitPair_preserving (n : ℕ) (μ : Fin (n+2) → Measure ℝ) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (splitPair n) (Measure.pi μ)
      (((μ 0).prod (μ 1)).prod (Measure.pi (fun i => μ i.succ.succ))) := by
  have h1 := measurePreserving_piFinSuccAbove μ 0
  have h2 := (MeasurePreserving.id (μ 0)).prod
    (measurePreserving_piFinSuccAbove (fun i : Fin (n+1) => μ i.succ) 0)
  have h3 := (measurePreserving_prodAssoc (μ 0) (μ 1)
    (Measure.pi fun i : Fin n => μ i.succ.succ)).symm
  exact h3.comp (h2.comp h1)

lemma splitPair_square_sum (n : ℕ) (x : Fin (n+2) → ℝ) :
    (∑ i, x i^2) = x 0^2 + x 1^2 + ∑ i : Fin n, x i.succ.succ^2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one]
  ring

section

lemma squareDisk_measurable (s : ℝ) : MeasurableSet (squareDisk s) := by
  exact measurableSet_le (by fun_prop) measurable_const

lemma squareAnnulus_measurable (s δ : ℝ) : MeasurableSet (squareAnnulus s δ) := by
  exact (measurableSet_lt measurable_const
    (show Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) by fun_prop)).inter
    (measurableSet_le (show Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) by fun_prop) measurable_const)

lemma squareDisk_complex {s : ℝ} (hs : 0 ≤ s) :
    Complex.measurableEquivRealProd ⁻¹' squareDisk s =
      Metric.closedBall (0 : ℂ) (Real.sqrt s) := by
  ext z
  simp only [Set.mem_preimage, squareDisk, Set.mem_ofPred_eq,
    Complex.measurableEquivRealProd_apply, Metric.mem_closedBall, dist_zero_right]
  rw [show z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 by rw [Complex.sq_norm, Complex.normSq_apply]; ring]
  exact (Real.le_sqrt (norm_nonneg _) hs).symm

lemma volume_squareDisk {s : ℝ} (hs : 0 ≤ s) :
    volume (squareDisk s) = ENNReal.ofReal (Real.pi * s) := by
  rw [← Complex.volume_preserving_equiv_real_prod.measure_preimage
    (squareDisk_measurable s).nullMeasurableSet, squareDisk_complex hs, Complex.volume_closedBall,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hs]
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul hs, mul_comm]

lemma squareAnnulus_sdiff (s δ : ℝ) :
    squareAnnulus s δ = squareDisk (s+δ) \ squareDisk s := by
  ext p
  simp [squareAnnulus, squareDisk, and_comm]

lemma volume_squareAnnulus {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    volume (squareAnnulus s δ) = ENNReal.ofReal (Real.pi * δ) := by
  rw [squareAnnulus_sdiff, measure_sdiff (by
    intro p hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ s at hp
    change p.1 ^ 2 + p.2 ^ 2 ≤ s+δ
    linarith) (squareDisk_measurable s).nullMeasurableSet (by
      rw [volume_squareDisk hs]
      exact ENNReal.ofReal_ne_top)]
  rw [volume_squareDisk (by linarith), volume_squareDisk hs,
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1
  ring

lemma gaussianPairPrefactor_nonneg (a b : ℝ≥0) : 0 ≤ gaussianPairPrefactor a b := by
  unfold gaussianPairPrefactor
  positivity

lemma gaussianPair_density (a b : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 a x * gaussianPDFReal 0 b y =
      gaussianPairPrefactor a b * Real.exp (-(x^2/(2*a) + y^2/(2*b))) := by
  simp only [gaussianPDFReal, sub_zero, gaussianPairPrefactor, mul_inv, neg_div]
  rw [show (Real.sqrt (2*Real.pi*a))⁻¹ * Real.exp (-(x^2/(2*a))) *
      ((Real.sqrt (2*Real.pi*b))⁻¹ * Real.exp (-(y^2/(2*b)))) =
      ((Real.sqrt (2*Real.pi*a))⁻¹ * (Real.sqrt (2*Real.pi*b))⁻¹) *
      (Real.exp (-(x^2/(2*a))) * Real.exp (-(y^2/(2*b)))) by ring,
    ← Real.exp_add, ← neg_add]

lemma gaussianPair_density_upper (a b : ℝ≥0) (x y : ℝ) :
    gaussianPDFReal 0 a x * gaussianPDFReal 0 b y ≤ gaussianPairPrefactor a b := by
  rw [gaussianPair_density]
  have h : Real.exp (-(x^2/(2*a) + y^2/(2*b))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left h (gaussianPairPrefactor_nonneg a b)

lemma gaussianPair_density_lower {a b : ℝ≥0} {m R x y : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) (hR : x^2+y^2 ≤ R) :
    gaussianPairPrefactor a b * Real.exp (-R/(2*m)) ≤
      gaussianPDFReal 0 a x * gaussianPDFReal 0 b y := by
  rw [gaussianPair_density]
  apply mul_le_mul_of_nonneg_left _ (gaussianPairPrefactor_nonneg a b)
  apply Real.exp_le_exp.mpr
  have hxa : x^2/(2*a) ≤ x^2/(2*m) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)
  have hyb : y^2/(2*b) ≤ y^2/(2*m) :=
    div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith)
  have hsum : x^2/(2*a) + y^2/(2*b) ≤ R/(2*m) := by
    calc
      _ ≤ x^2/(2*m) + y^2/(2*m) := add_le_add hxa hyb
      _ = (x^2+y^2)/(2*m) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hR (by positivity)
  rw [neg_div]
  exact neg_le_neg hsum

lemma gaussianPair_apply {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) (s : Set (ℝ × ℝ)) :
    ((gaussianReal 0 a).prod (gaussianReal 0 b)) s =
      ∫⁻ p in s, ENNReal.ofReal (gaussianPDFReal 0 a p.1 * gaussianPDFReal 0 b p.2) := by
  rw [gaussianReal_of_var_ne_zero _ ha, gaussianReal_of_var_ne_zero _ hb,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    withDensity_apply' _ s]
  apply lintegral_congr
  intro p
  exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)).symm

lemma gaussianPair_annulus_lower {a b : ℝ≥0} {m s δ : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) (hs : 0 ≤ s) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b * Real.exp (-(s+δ)/(2*m))) ≤
      ((gaussianReal 0 a).prod (gaussianReal 0 b)) (squareAnnulus s δ) := by
  have ha : a ≠ 0 := by intro h; simp only [h, NNReal.coe_zero] at hma; linarith
  have hb : b ≠ 0 := by intro h; simp only [h, NNReal.coe_zero] at hmb; linarith
  rw [gaussianPair_apply ha hb]
  calc
    _ = ∫⁻ _p in squareAnnulus s δ,
        ENNReal.ofReal (gaussianPairPrefactor a b * Real.exp (-(s+δ)/(2*m))) := by
      rw [lintegral_const, Measure.restrict_apply_univ, volume_squareAnnulus hs hδ,
        ← ENNReal.ofReal_mul (mul_nonneg (gaussianPairPrefactor_nonneg _ _)
          (Real.exp_pos _).le)]
      congr 1
      ring
    _ ≤ _ := by
      apply lintegral_mono_ae
      apply (ae_restrict_iff' (squareAnnulus_measurable s δ)).mpr
      exact ae_of_all _ (fun p hp => ENNReal.ofReal_le_ofReal
        (gaussianPair_density_lower hm hma hmb hp.2))

lemma volume_squareAnnulus_le {s δ : ℝ} (hδ : 0 ≤ δ) :
    volume (squareAnnulus s δ) ≤ ENNReal.ofReal (Real.pi * δ) := by
  by_cases hs : 0 ≤ s
  · exact le_of_eq (volume_squareAnnulus hs hδ)
  · have hsn : s < 0 := lt_of_not_ge hs
    by_cases ht : 0 ≤ s+δ
    · have hsub : squareAnnulus s δ ⊆ squareDisk (s+δ) := fun _ h => h.2
      calc
        _ ≤ volume (squareDisk (s+δ)) := measure_mono hsub
        _ = ENNReal.ofReal (Real.pi*(s+δ)) := volume_squareDisk ht
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
    · have hset : squareAnnulus s δ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hh := add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)
        exact ht (le_trans hh hp.2)
      rw [hset, measure_empty]
      exact bot_le

lemma gaussianPair_annulus_upper_all {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((gaussianReal 0 a).prod (gaussianReal 0 b)) (squareAnnulus s δ) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) := by
  rw [gaussianPair_apply ha hb]
  calc
    _ ≤ ∫⁻ _p in squareAnnulus s δ, ENNReal.ofReal (gaussianPairPrefactor a b) := by
      exact lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (gaussianPair_density_upper a b p.1 p.2))
    _ ≤ ENNReal.ofReal (gaussianPairPrefactor a b) * ENNReal.ofReal (Real.pi * δ) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact mul_le_mul_of_nonneg_left (volume_squareAnnulus_le hδ) bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (gaussianPairPrefactor_nonneg _ _), mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sumSquareShell_measurable {Z : Ω → ℝ} (hZ : Measurable Z) (s δ : ℝ) :
    MeasurableSet (sumSquareShell Z s δ) := by
  have h : Measurable (fun p : (ℝ × ℝ) × Ω => p.1.1^2 + p.1.2^2 + Z p.2) := by fun_prop
  exact (measurableSet_lt measurable_const h).inter (measurableSet_le h measurable_const)

lemma sumSquareShell_apply (μ : Measure (ℝ × ℝ)) (ν : Measure Ω) [SFinite μ] [SFinite ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) (s δ : ℝ) :
    (μ.prod ν) (sumSquareShell Z s δ) = ∫⁻ ω, μ (squareAnnulus (s-Z ω) δ) ∂ν := by
  rw [Measure.prod_apply_symm (sumSquareShell_measurable hZ s δ)]
  apply lintegral_congr
  intro ω
  congr 1
  ext p
  simp only [Set.mem_preimage, sumSquareShell, squareAnnulus, Set.mem_ofPred_eq]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma gaussianPair_bulk_lower {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) {a b : ℝ≥0} {m s R δ : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b * Real.exp (-(R+δ)/(2*m))) *
      ν {ω | s-R ≤ Z ω ∧ Z ω ≤ s} ≤
      (((gaussianReal 0 a).prod (gaussianReal 0 b)).prod ν) (sumSquareShell Z s δ) := by
  rw [sumSquareShell_apply _ _ hZ]
  let A := {ω | s-R ≤ Z ω ∧ Z ω ≤ s}
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const hZ).inter (measurableSet_le hZ measurable_const)
  calc
    _ = ∫⁻ _ω in A, ENNReal.ofReal
        (Real.pi * δ * gaussianPairPrefactor a b * Real.exp (-(R+δ)/(2*m))) ∂ν := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ ω in A, ((gaussianReal 0 a).prod (gaussianReal 0 b))
        (squareAnnulus (s-Z ω) δ) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with ω hω
      apply le_trans _ (gaussianPair_annulus_lower hm hma hmb (sub_nonneg.mpr hω.2) hδ)
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg Real.pi_pos.le hδ) (gaussianPairPrefactor_nonneg _ _))
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2*m)).mpr
      linarith [hω.1]
    _ ≤ _ := setLIntegral_le_lintegral _ _

end

section

lemma fourth_power_le_exp (x : ℝ) : x ^ 4 ≤ 32 * Real.exp (x^2/4) := by
  have h := Real.pow_div_factorial_le_exp (x^2/4) (by positivity) 2
  norm_num at h
  nlinarith

lemma gaussian_fourth_integrable : Integrable (fun x : ℝ => x^4) (gaussianReal 0 1) := by
  apply ((gaussian_square_integrable (1/4) (by norm_num)).const_mul 32).mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x^4)]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using fourth_power_le_exp x

lemma gaussian_fourth_bound : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) ≤ 64 := by
  calc
    _ ≤ ∫ x : ℝ, 32 * Real.exp ((1/4) * x^2) ∂gaussianReal 0 1 :=
      integral_mono gaussian_fourth_integrable
        ((gaussian_square_integrable (1/4) (by norm_num)).const_mul 32)
        (fun x => by simpa only [div_eq_mul_inv, one_mul, mul_comm] using fourth_power_le_exp x)
    _ = 32 * (Real.sqrt (1/2))⁻¹ := by
      rw [integral_const_mul, gaussian_square_integral _ (by norm_num)]
      norm_num
    _ ≤ 64 := by
      have hs : (1/2 : ℝ) ≤ Real.sqrt (1/2) := by
        apply Real.le_sqrt (by norm_num) (by norm_num) |>.mpr
        norm_num
      have hh : (Real.sqrt (1/2))⁻¹ ≤ 2 := by
        calc
          _ ≤ (1/2 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).mpr hs
          _ = 2 := by norm_num
      linarith

lemma gaussian_as_scaled (v : ℝ≥0) : gaussianReal 0 v =
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt v.coe_nonneg]

lemma gaussian_fourth_integrable_var (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^4) (gaussianReal 0 v) := by
  rw [gaussian_as_scaled]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, mul_pow] using gaussian_fourth_integrable.const_mul ((Real.sqrt v)^4)

lemma gaussian_fourth_bound_var (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) ≤ 64 * (v:ℝ)^2 := by
  rw [gaussian_as_scaled, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hs : (Real.sqrt (v:ℝ))^4 = (v:ℝ)^2 := by
    rw [show (4:ℕ)=2*2 by rfl, pow_mul, Real.sq_sqrt v.coe_nonneg]
  rw [hs]
  exact (mul_le_mul_of_nonneg_left gaussian_fourth_bound (sq_nonneg (v:ℝ))).trans_eq (mul_comm _ _)

lemma gaussian_square_memLp (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using gaussian_fourth_integrable_var v

lemma gaussian_square_mean (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = v := by
  have h := variance_eq_sub (μ := gaussianReal 0 v) (X := id) (memLp_id_gaussianReal 2)
  simpa only [variance_id_gaussianReal, id_eq, Pi.pow_apply, integral_id_gaussianReal,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h.symm

lemma gaussian_square_variance (v : ℝ≥0) :
    Var[(fun x : ℝ => x^2); gaussianReal 0 v] ≤ 64 * (v:ℝ)^2 := by
  rw [variance_eq_sub (gaussian_square_memLp v), gaussian_square_mean]
  have h : (∫ x : ℝ, (x^2)^2 ∂gaussianReal 0 v) ≤ 64 * (v:ℝ)^2 := by
    simpa only [← pow_mul] using gaussian_fourth_bound_var v
  simpa only [Pi.pow_apply] using (sub_le_self _ (sq_nonneg (v:ℝ))).trans h

variable {ι : Type*} [Fintype ι]

lemma piSquareSum_memLp (v : ι → ℝ≥0) :
    MemLp (piSquareSum (ι := ι)) 2 (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  exact memLp_finsetSum _ (fun i _ => (gaussian_square_memLp (v i)).comp_measurePreserving
    (measurePreserving_eval _ i))

lemma piSquareSum_mean (v : ι → ℝ≥0) :
    (∫ x, piSquareSum x ∂Measure.pi (fun i => gaussianReal 0 (v i))) = ∑ i, (v i : ℝ) := by
  unfold piSquareSum
  rw [integral_finsetSum Finset.univ (f := fun (i : ι) (x : ι → ℝ) => x i ^ 2)
    (fun i _ => integrable_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i)
      ((gaussian_square_memLp (v i)).integrable (by norm_num)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_comp_eval (μ := fun i => gaussianReal 0 (v i)) (i := i) (f := fun x : ℝ => x^2) (by fun_prop)]
  exact gaussian_square_mean (v i)

lemma piSquareSum_variance (v : ι → ℝ≥0) :
    Var[piSquareSum (ι := ι); Measure.pi (fun i => gaussianReal 0 (v i))] ≤
      64 * ∑ i, (v i : ℝ)^2 := by
  have he : piSquareSum (ι := ι) = ∑ i, (fun x : ι → ℝ => x i^2) := by
    funext x
    simp only [piSquareSum, Finset.sum_apply]
  rw [he, variance_sum_pi (X := fun (_ : ι) (x : ℝ) => x^2)
    (fun i => gaussian_square_memLp (v i)), Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => gaussian_square_variance (v i))

lemma piSquareSum_tail (v : ι → ℝ≥0) {d : ℝ} (hd : 0 < d) :
    (Measure.pi (fun i => gaussianReal 0 (v i))) {x | d ≤ |piSquareSum x - ∑ i, (v i : ℝ)|} ≤
      ENNReal.ofReal (64 * (∑ i, (v i : ℝ)^2) / d^2) := by
  have ht := meas_ge_le_variance_div_sq (piSquareSum_memLp v) hd
  rw [piSquareSum_mean] at ht
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right (piSquareSum_variance v) (sq_nonneg d)

lemma piSquareSum_bulk_mass (v : ι → ℝ≥0) {s d : ℝ} (hd : 0 < d)
    (hmean : (∑ i, (v i : ℝ)) = s-d)
    (hvar : 128 * (∑ i, (v i : ℝ)^2) ≤ d^2) :
    (1/2 : ℝ≥0∞) ≤ (Measure.pi (fun i => gaussianReal 0 (v i)))
      {x | s-2*d ≤ piSquareSum x ∧ piSquareSum x ≤ s} := by
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  let A := {x : ι → ℝ | s-2*d ≤ piSquareSum x ∧ piSquareSum x ≤ s}
  have hA : MeasurableSet A := by
    have hS : Measurable (piSquareSum (ι := ι)) := by unfold piSquareSum; fun_prop
    exact (measurableSet_le measurable_const hS).inter (measurableSet_le hS measurable_const)
  have hsub : Aᶜ ⊆ {x : ι → ℝ | d ≤ |piSquareSum x - ∑ i, (v i : ℝ)|} := by
    intro x hx
    change ¬ (s-2*d ≤ piSquareSum x ∧ piSquareSum x ≤ s) at hx
    rw [Set.mem_ofPred_eq, hmean, le_abs]
    push Not at hx
    by_cases hh : s-2*d ≤ piSquareSum x
    · left; linarith [hx hh]
    · right; linarith
  have ht : μ Aᶜ ≤ (1/2:ℝ≥0∞) := by
    apply (measure_mono hsub).trans ((piSquareSum_tail v hd).trans _)
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    linarith
  have hsum : μ A + μ Aᶜ = 1 := by
    rw [measure_add_measure_compl hA, measure_univ]
  have hfin : μ A ≠ ∞ := measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hfin (measure_ne_top _ _), ENNReal.toReal_one] at hreal
  have ht' := ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞) ≠ ∞) ht
  norm_num at ht'
  apply (ENNReal.toReal_le_toReal (by norm_num) hfin).mp
  norm_num
  linarith

end

section

open Set Filter

variable {n : ℕ}

lemma diagonalGaussian_shell_split (v : Fin (n+2) → ℝ≥0) (s δ : ℝ) :
    diagonalGaussian v (squareNormShell s δ) =
      (((gaussianReal 0 (v 0)).prod (gaussianReal 0 (v 1))).prod
        (Measure.pi fun i : Fin n => gaussianReal 0 (v i.succ.succ)))
      (sumSquareShell piSquareSum s δ) := by
  rw [diagonalGaussian, Measure.map_apply (WithLp.measurable_toLp 2 _)
    (squareNormShell_measurable s δ)]
  rw [← (splitPair_preserving n (fun i => gaussianReal 0 (v i))).measure_preimage
    (sumSquareShell_measurable (by unfold piSquareSum; fun_prop) s δ).nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_preimage, squareNormShell, sumSquareShell, Set.mem_ofPred_eq,
    EuclideanSpace.real_norm_sq_eq, splitPair, piSquareSum]
  rw [splitPair_square_sum]

lemma diagonalGaussian_shell_lower (v : Fin (n+2) → ℝ≥0) {m s d δ : ℝ}
    (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1) (hδ : 0 ≤ δ) (hd : 0 < d)
    (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = s-d)
    (hvar : 128 * (∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
    ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m)) / 2) ≤ diagonalGaussian v (squareNormShell s δ) := by
  rw [diagonalGaussian_shell_split]
  have hl := gaussianPair_bulk_lower
    (ν := Measure.pi fun i : Fin n => gaussianReal 0 (v i.succ.succ))
    (Z := piSquareSum) (by unfold piSquareSum; fun_prop) (s := s) (R := 2*d)
    hm hm0 hm1 hδ
  have hp := piSquareSum_bulk_mass (fun i : Fin n => v i.succ.succ) hd hmean hvar
  apply le_trans _ hl
  calc
    _ = ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m))) * (1/2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]
        congr 1
        norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hp bot_le

lemma diagonalSquareDensity_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun δ : ℝ => (diagonalGaussian v (squareNormShell s δ)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (diagonalSquareDensity v s)) := by
  rw [diagonalGaussian_density v hv]
  exact squareNormShell_density_limit volume (euclideanGaussianPDF_integrable v)
    (euclideanGaussianPDF_continuous v) (fun x => gaussianPiPDF_nonneg v x) hs

lemma diagonalSquareDensity_lower (v : Fin (n+2) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {m s d : ℝ} (hs : 0 < s) (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1)
    (hd : 0 < d) (hmean : (∑ i : Fin n, (v i.succ.succ : ℝ)) = s-d)
    (hvar : 128 * (∑ i : Fin n, (v i.succ.succ : ℝ)^2) ≤ d^2) :
    Real.pi * gaussianPairPrefactor (v 0) (v 1) * Real.exp (-d/m) / 2 ≤
      diagonalSquareDensity v s := by
  have hc : Continuous (fun δ : ℝ => Real.pi * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m)) / 2) := by fun_prop
  have ht := (hc.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have ht' : Tendsto (fun δ : ℝ => Real.pi * gaussianPairPrefactor (v 0) (v 1) *
      Real.exp (-(2*d+δ)/(2*m)) / 2) (nhdsWithin 0 (Ioi 0))
      (𝓝 (Real.pi * gaussianPairPrefactor (v 0) (v 1) * Real.exp (-d/m) / 2)) := by
    have he : -(2*d+(0:ℝ))/(2*m) = -d/m := by ring
    simpa only [he] using ht
  apply le_of_tendsto_of_tendsto ht' (diagonalSquareDensity_limit v hv hs)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (diagonalGaussian_shell_lower v hm hm0 hm1 hδ0.le hd hmean hvar)
  have hp := gaussianPairPrefactor_nonneg (v 0) (v 1)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  apply (le_div_iff₀ hδ0).mpr
  nlinarith

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma radialEval_embedding : MeasurableEmbedding (radialEval (E := E)) := by
  exact (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).comp
    (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E).symm)

lemma radialCone_measurable {A : Set (sphere (0 : E) 1)} (hA : MeasurableSet A) :
    MeasurableSet (radialCone A) := radialEval_embedding.measurableSet_image' (hA.prod .univ)

lemma radialCone_mem (A : Set (sphere (0 : E) 1)) (r : Ioi (0 : ℝ)) (u : sphere (0 : E) 1) :
    r.val • u.val ∈ radialCone A ↔ u ∈ A := by
  have h := radialEval_embedding.injective.mem_set_image (s := A ×ˢ Set.univ) (a := (u,r))
  simpa only [radialCone, radialEval, Set.mem_prod, Set.mem_univ, and_true] using h

lemma angular_indicator_integral (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → ℝ)
    {A : Set (sphere (0 : E) 1)} (hA : MeasurableSet A) {r : ℝ} (hr : 0 < r) :
    (∫ u : sphere (0 : E) 1, (radialCone A).indicator f (r • u.val) ∂μ.toSphere) =
      ∫ u in A, f (r • u.val) ∂μ.toSphere := by
  rw [← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards with u
  have hh := radialCone_mem A ⟨r, hr⟩ u
  by_cases hu : u ∈ A
  · simp only [Set.indicator_of_mem hu, Set.indicator_of_mem (hh.mpr hu)]
  · simp only [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h => hu (hh.mp h))]

lemma radialDensityOn_continuous (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Continuous f) (A : Set (sphere (0 : E) 1)) :
    Continuous (radialDensityOn μ f A) :=
  (continuous_id.pow _).mul (angular_integral_continuous μ hf A)

variable [Nontrivial E]

lemma normShell_cone_density_real (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ}
    (hf : Integrable f μ) (hfn : ∀ x, 0 ≤ f x) {A : Set (sphere (0 : E) 1)}
    (hA : MeasurableSet A) {a b : ℝ} (ha : 0 ≤ a) :
    (μ.withDensity (fun x => ENNReal.ofReal (f x)) (normShell a b ∩ radialCone A)).toReal =
      ∫ r in Ioc a b, radialDensityOn μ f A r := by
  have hind : (fun x => ENNReal.ofReal ((radialCone A).indicator f x)) =
      (radialCone A).indicator (fun x => ENNReal.ofReal (f x)) := by
    funext x
    by_cases h : x ∈ radialCone A <;> simp [h]
  have hw := normShell_density_real μ (hf.indicator (radialCone_measurable hA))
    (fun x => Set.indicator_nonneg (fun x _ => hfn x) x) (b := b) ha
  rw [hind, withDensity_indicator (radialCone_measurable hA),
    ← restrict_withDensity (radialCone_measurable hA),
    Measure.restrict_apply (normShell_measurable a b)] at hw
  rw [hw]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  simp only [radialDensity, radialDensityOn,
    angular_indicator_integral μ f hA (lt_of_le_of_lt ha hr.1)]

lemma squareNormShell_cone_density_limit (μ : Measure E) [μ.IsAddHaarMeasure] [ProperSpace E]
    {f : E → ℝ} (hf : Integrable f μ) (hfc : Continuous f) (hfn : ∀ x, 0 ≤ f x)
    {A : Set (sphere (0 : E) 1)} (hA : MeasurableSet A) {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun δ : ℝ =>
      (μ.withDensity (fun x => ENNReal.ofReal (f x)) (squareNormShell s δ ∩ radialCone A)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (radialDensityOn μ f A (Real.sqrt s) / (2 * Real.sqrt s))) := by
  have hq := radialDensityOn_continuous μ hfc A
  have hd : HasDerivAt (fun t : ℝ => ∫ r in Real.sqrt s..t, radialDensityOn μ f A r)
      (radialDensityOn μ f A (Real.sqrt s)) (Real.sqrt s) :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hd' := hd.comp s (Real.hasDerivAt_sqrt hs.ne')
  have hh := hd'.tendsto_slope_zero_right
  simp only [Function.comp_def, mul_one_div] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  rw [squareNormShell_eq hs.le hδ0.le,
    normShell_cone_density_real μ hf hfn hA (Real.sqrt_nonneg _), intervalIntegral.integral_same,
    sub_zero, smul_eq_mul, intervalIntegral.integral_of_le (Real.sqrt_le_sqrt (by linarith))]
  exact mul_comm _ _

end

section

variable {Ω : Type*} [MeasurableSpace Ω]

lemma gaussianPair_bulk_restricted_upper {ν : Measure Ω} [SFinite ν]
    {Z : Ω → ℝ} (hZ : Measurable Z) {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    {B : Set Ω} (hB : MeasurableSet B) (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((gaussianReal 0 a).prod (gaussianReal 0 b)).prod ν)
      (sumSquareShell Z s δ ∩ Prod.snd ⁻¹' B) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor a b) * ν B := by
  rw [Measure.prod_apply_symm ((sumSquareShell_measurable hZ s δ).inter
    (hB.preimage measurable_snd)), ← Measure.restrict_apply_univ (μ := ν) (s := B),
    ← lintegral_const, ← lintegral_indicator hB]
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ B
  · rw [Set.indicator_of_mem hω]
    convert gaussianPair_annulus_upper_all ha hb (s-Z ω) hδ using 2
    all_goals try with_reducible_and_instances rfl
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, sumSquareShell, squareAnnulus,
      Set.mem_ofPred_eq, hω, and_true]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  · rw [Set.indicator_of_notMem hω]
    suffices he : (fun p : ℝ × ℝ => (p, ω)) ⁻¹' (sumSquareShell Z s δ ∩ Prod.snd ⁻¹' B) = ∅ by
      dsimp only
      rw [he, measure_empty]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hω hp.2

lemma gaussian_density_upper (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  rw [sub_zero]
  have h : Real.exp (-(x^2/(2*v))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  simpa only [neg_div, mul_one] using mul_le_mul_of_nonneg_left h (by positivity :
    0 ≤ (Real.sqrt (2*Real.pi*v))⁻¹)

lemma gaussian_smallBall_upper {v : ℝ≥0} (hv : v ≠ 0) (T : ℝ) :
    gaussianReal 0 v {x : ℝ | |x| ≤ T} ≤
      ENNReal.ofReal (2*T*(Real.sqrt (2*Real.pi*v))⁻¹) := by
  have he : {x : ℝ | |x| ≤ T} = Set.Icc (-T) T := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  rw [he, gaussianReal_of_var_ne_zero _ hv, withDensity_apply _ measurableSet_Icc]
  calc
    _ ≤ ∫⁻ _x in Set.Icc (-T) T, ENNReal.ofReal ((Real.sqrt (2*Real.pi*v))⁻¹) := by
      exact lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (gaussian_density_upper v x))
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end

open Set Filter

variable {n : ℕ}

lemma diagonalGaussian_shell_restricted_upper (v : Fin (n+2) → ℝ≥0)
    (h0 : v 0 ≠ 0) (h1 : v 1 ≠ 0) {B : Set (Fin n → ℝ)} (hB : MeasurableSet B)
    (s : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    diagonalGaussian v (squareNormShell s δ ∩
      {x : EuclideanSpace ℝ (Fin (n+2)) | (fun i : Fin n => x i.succ.succ) ∈ B}) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1)) *
        (Measure.pi fun i : Fin n => gaussianReal 0 (v i.succ.succ)) B := by
  have hB' : MeasurableSet {x : EuclideanSpace ℝ (Fin (n+2)) |
      (fun i : Fin n => x i.succ.succ) ∈ B} := hB.preimage (by fun_prop)
  rw [diagonalGaussian, Measure.map_apply (WithLp.measurable_toLp 2 _)
    ((squareNormShell_measurable s δ).inter hB')]
  have he : (WithLp.toLp 2 : (Fin (n+2) → ℝ) → EuclideanSpace ℝ (Fin (n+2))) ⁻¹'
      (squareNormShell s δ ∩ {x | (fun i : Fin n => x i.succ.succ) ∈ B}) =
      splitPair n ⁻¹' (sumSquareShell piSquareSum s δ ∩ Prod.snd ⁻¹' B) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, squareNormShell, sumSquareShell,
      Set.mem_ofPred_eq, EuclideanSpace.real_norm_sq_eq, splitPair, piSquareSum]
    rw [splitPair_square_sum]
  rw [he, (splitPair_preserving n (fun i => gaussianReal 0 (v i))).measure_preimage
    ((sumSquareShell_measurable (by unfold piSquareSum; fun_prop) s δ).inter
      (hB.preimage measurable_snd)).nullMeasurableSet]
  exact gaussianPair_bulk_restricted_upper (by unfold piSquareSum; fun_prop) h0 h1 hB s hδ

lemma radialCone_coordinate_bound {ι : Type*} [Fintype ι] {i : ι} {b K : ℝ}
    (hb : 0 ≤ b) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ radialCone {u : sphere (0 : EuclideanSpace ℝ ι) 1 | |u.val i| ≤ b})
    (hn : ‖x‖^2 ≤ K) : |x i| ≤ b * Real.sqrt K := by
  rcases hx with ⟨⟨u,r⟩, ⟨hu,_⟩, rfl⟩
  have hr0 : 0 < r.val := r.property
  have hu' : |u.val i| ≤ b := hu
  have huN : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hn' : r.val^2 ≤ K := by
    simpa only [radialEval, norm_smul, Real.norm_eq_abs, abs_of_pos hr0, huN, mul_one] using hn
  have hK : 0 ≤ K := (sq_nonneg r.val).trans hn'
  have hr : r.val ≤ Real.sqrt K := (Real.le_sqrt hr0.le hK).mpr hn'
  change |(r.val • u.val) i| ≤ _
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr0]
  exact (mul_le_mul_of_nonneg_left hu' hr0.le).trans (by nlinarith)

lemma diagonalGaussian_shell_cone_upper (v : Fin (n+3) → ℝ≥0)
    (hv : ∀ i, v i ≠ 0) {s δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) :
    diagonalGaussian v (squareNormShell s δ ∩
      radialCone {u : sphere (0 : EuclideanSpace ℝ (Fin (n+3))) 1 |
        |u.val (0 : Fin (n+1)).succ.succ| ≤ b}) ≤
      ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1) *
        (2*(b*Real.sqrt (s+δ))*(Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹)) := by
  let B := {x : Fin (n+1) → ℝ | |x 0| ≤ b * Real.sqrt (s+δ)}
  have hB : MeasurableSet B := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hsub : squareNormShell s δ ∩
      radialCone {u : sphere (0 : EuclideanSpace ℝ (Fin (n+3))) 1 |
        |u.val (0 : Fin (n+1)).succ.succ| ≤ b} ⊆
      squareNormShell s δ ∩
        {x : EuclideanSpace ℝ (Fin (n+3)) | (fun i : Fin (n+1) => x i.succ.succ) ∈ B} := by
    intro x hx
    exact ⟨hx.1, radialCone_coordinate_bound hb hx.2 hx.1.2⟩
  apply (measure_mono hsub).trans
  apply (diagonalGaussian_shell_restricted_upper v (hv 0) (hv 1) hB s hδ).trans
  have he : (Measure.pi fun i : Fin (n+1) => gaussianReal 0 (v i.succ.succ)) B =
      gaussianReal 0 (v (0 : Fin (n+1)).succ.succ) {y : ℝ | |y| ≤ b*Real.sqrt (s+δ)} := by
    exact (measurePreserving_eval (fun i : Fin (n+1) => gaussianReal 0 (v i.succ.succ)) 0).measure_preimage
      (measurableSet_le (measurable_id.abs) measurable_const).nullMeasurableSet
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (Real.pi * δ * gaussianPairPrefactor (v 0) (v 1)) *
        ENNReal.ofReal (2*(b*Real.sqrt (s+δ))*(Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹) :=
      mul_le_mul_of_nonneg_left (gaussian_smallBall_upper (hv _) _) bot_le
    _ = _ := (ENNReal.ofReal_mul (by
      exact mul_nonneg (mul_nonneg Real.pi_pos.le hδ) (gaussianPairPrefactor_nonneg _ _))).symm

lemma diagonalSquareDensityOn_limit {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {A : Set (sphere (0 : EuclideanSpace ℝ ι) 1)} (hA : MeasurableSet A)
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun δ : ℝ => (diagonalGaussian v (squareNormShell s δ ∩ radialCone A)).toReal / δ)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (diagonalSquareDensityOn v A s)) := by
  rw [diagonalGaussian_density v hv]
  exact squareNormShell_cone_density_limit volume (euclideanGaussianPDF_integrable v)
    (euclideanGaussianPDF_continuous v) (fun x => gaussianPiPDF_nonneg v x) hA hs

lemma diagonalSquareDensityOn_smallBall (v : Fin (n+3) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    {s b : ℝ} (hs : 0 < s) (hb : 0 ≤ b) :
    diagonalSquareDensityOn v
      {u : sphere (0 : EuclideanSpace ℝ (Fin (n+3))) 1 |
        |u.val (0 : Fin (n+1)).succ.succ| ≤ b} s ≤
      Real.pi * gaussianPairPrefactor (v 0) (v 1) *
        (2*(b*Real.sqrt s)*(Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹) := by
  have hc : Continuous (fun δ : ℝ => Real.pi * gaussianPairPrefactor (v 0) (v 1) *
      (2*(b*Real.sqrt (s+δ))*(Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹)) := by fun_prop
  have ht := (hc.continuousAt (x := 0)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simp only [add_zero] at ht
  apply le_of_tendsto_of_tendsto
    (diagonalSquareDensityOn_limit v hv (measurableSet_le (by fun_prop) measurable_const) hs) ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : 0 < δ := hδ.out
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (diagonalGaussian_shell_cone_upper v hv (s := s) hδ0.le hb)
  have hp := gaussianPairPrefactor_nonneg (v 0) (v 1)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  apply (div_le_iff₀ hδ0).mpr
  nlinarith

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussianPiPDF_exp (v : ι → ℝ≥0) (x : ι → ℝ) :
    gaussianPiPDF v x = gaussianPiPrefactor v * Real.exp (-∑ i, x i ^ 2 / (2*v i)) := by
  simp only [gaussianPiPDF, gaussianPDFReal, sub_zero, Finset.prod_mul_distrib,
    gaussianPiPrefactor, ← Real.exp_sum, ← Finset.sum_neg_distrib, neg_div]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_pos {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    0 < gaussianPiPrefactor v := by
  apply Finset.prod_pos
  intro i _
  have hvi : 0 < (v i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
  positivity

omit [Nonempty ι] in
lemma unitSphere_sum_sq (u : unitSphere ι) : ∑ i, u.val i ^ 2 = 1 := by
  have hn : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [hn, one_pow] using (EuclideanSpace.real_norm_sq_eq u.val).symm

omit [Nonempty ι] in
lemma sphereGaussianPDF {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (r : ℝ) (u : unitSphere ι) :
    gaussianPiPDF v (WithLp.ofLp (r • u.val)) = gaussianPiPrefactor v * Real.exp (-z*r^2/2) *
      Real.exp (a/2 * diagonalEnergy lam (r • u.val)) := by
  rw [gaussianPiPDF_exp, mul_assoc, ← Real.exp_add]
  congr 2
  have hsum : ∑ i, (r • u.val) i ^ 2 / (2 * v i) =
      z*r^2/2 - a/2 * diagonalEnergy lam (r • u.val) := by
    simp only [diagonalEnergy, PiLp.smul_apply, smul_eq_mul]
    calc
      _ = ∑ i, (z*r^2/2 * u.val i^2 - a/2 * (lam i*(r*u.val i)^2)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [div_eq_mul_inv, mul_inv, hq i]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, unitSphere_sum_sq, mul_one,
          ← Finset.mul_sum]
  rw [hsum]
  ring

lemma spherePartition_pos (lam : ι → ℝ) (a r : ℝ) : 0 < spherePartition lam a r := by
  apply div_pos _ sphereArea_pos
  have hc : Continuous (fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val))) := by
    unfold diagonalEnergy
    fun_prop
  have hi : Integrable (fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val)))
      (volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  let _ : NeZero (volume : Measure (EuclideanSpace ℝ ι)).toSphere := ⟨Measure.toSphere_ne_zero _⟩
  exact integral_exp_pos hi

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma sphereWeight_integrable (lam : ι → ℝ) (a r : ℝ) :
    Integrable (fun u : unitSphere ι => Real.exp (a / 2 * diagonalEnergy lam (r • u.val)))
      (volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
  have hc : Continuous (fun u : unitSphere ι => Real.exp (a / 2 * diagonalEnergy lam (r • u.val))) := by
    unfold diagonalEnergy; fun_prop
  simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ

lemma sphereWeight_integral_pos (lam : ι → ℝ) (a r : ℝ) :
    0 < ∫ u : unitSphere ι, Real.exp (a/2 * diagonalEnergy lam (r • u.val))
      ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere := by
  have h := spherePartition_pos lam a r
  exact (div_pos_iff.mp h).elim (fun h => h.1)
    (fun h => False.elim (not_lt_of_ge (sphereArea_pos (ι := ι)).le h.2))

instance sphereTilted_probability (lam : ι → ℝ) (a r : ℝ) :
    IsProbabilityMeasure (sphereTilted lam a r) := by
  constructor
  rw [sphereTilted, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal (sphereWeight_integrable lam a r)
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (sphereWeight_integral_pos lam a r)))
    ENNReal.ofReal_ne_top

lemma sphereTilted_apply_real (lam : ι → ℝ) (a r : ℝ) {A : Set (unitSphere ι)} (hA : MeasurableSet A) :
    (sphereTilted lam a r A).toReal =
      (∫ u in A, Real.exp (a/2 * diagonalEnergy lam (r • u.val))
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) /
      (∫ u : unitSphere ι, Real.exp (a/2 * diagonalEnergy lam (r • u.val))
        ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) := by
  rw [sphereTilted, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal (sphereWeight_integrable lam a r).integrableOn
      (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)),
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (sphereWeight_integral_pos lam a r).le,
    ENNReal.toReal_ofReal (integral_nonneg (fun u => (Real.exp_pos _).le))]
  ring

lemma sphereTilted_density_ratio {lam : ι → ℝ} {v : ι → ℝ≥0} {z a s : ℝ}
    (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i : ℝ)⁻¹ = z - a * lam i) (hs : 0 < s)
    {A : Set (unitSphere ι)} (hA : MeasurableSet A) :
    (sphereTilted lam a (Real.sqrt s) A).toReal =
      diagonalSquareDensityOn v A s / diagonalSquareDensity v s := by
  rw [sphereTilted_apply_real lam a _ hA]
  unfold diagonalSquareDensityOn diagonalSquareDensity radialDensityOn radialDensity
  simp_rw [sphereGaussianPDF hq]
  rw [integral_const_mul, integral_const_mul]
  have h1 := ne_of_gt (gaussianPiPrefactor_pos hv)
  have h2 := ne_of_gt (Real.exp_pos (-z*(Real.sqrt s)^2/2))
  have h3 := ne_of_gt (pow_pos (Real.sqrt_pos.mpr hs) (Module.finrank ℝ (EuclideanSpace ℝ ι) - 1))
  have h4 := ne_of_gt (sphereWeight_integral_pos lam a (Real.sqrt s))
  have h5 := ne_of_gt (Real.sqrt_pos.mpr hs)
  field_simp

end

section

variable {n : ℕ}

lemma gaussianPairPrefactor_pos {a b : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < gaussianPairPrefactor a b := by
  have ha' : 0 < (a:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
  have hb' : 0 < (b:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hb)
  unfold gaussianPairPrefactor
  positivity

lemma sphereTilted_smallBall_s2_oai (lam : Fin (n+3) → ℝ) (a z : ℝ)
    (v : Fin (n+3) → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (hq : ∀ i, (v i : ℝ)⁻¹ = z-a*lam i)
    {s m d b : ℝ} (hs : 0 < s) (hm : 0 < m) (hm0 : m ≤ v 0) (hm1 : m ≤ v 1)
    (hd : 0 < d) (hb : 0 ≤ b)
    (hmean : (∑ i : Fin (n+1), (v i.succ.succ : ℝ)) = s-d)
    (hvar : 128 * (∑ i : Fin (n+1), (v i.succ.succ : ℝ)^2) ≤ d^2) :
    (sphereTilted lam a (Real.sqrt s)
      {u : unitSphere (Fin (n+3)) | |u.val (0 : Fin (n+1)).succ.succ| ≤ b}).toReal ≤
      4 * (b * Real.sqrt s) * (Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹ *
        Real.exp (d/m) := by
  rw [sphereTilted_density_ratio hv hq hs (measurableSet_le (by fun_prop) measurable_const)]
  have hl := diagonalSquareDensity_lower v hv hs hm hm0 hm1 hd hmean hvar
  have hu := diagonalSquareDensityOn_smallBall v hv hs hb
  have hP := mul_pos Real.pi_pos (gaussianPairPrefactor_pos (hv 0) (hv 1))
  have hp : 0 < diagonalSquareDensity v s :=
    (div_pos (mul_pos hP (Real.exp_pos _)) (by norm_num)).trans_le hl
  apply (div_le_iff₀ hp).mpr
  have hC : 0 ≤ 4 * (b*Real.sqrt s) *
      (Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹ * Real.exp (d/m) := by positivity
  apply hu.trans
  apply le_trans _ (mul_le_mul_of_nonneg_left hl hC)
  have he : Real.exp (d/m) * Real.exp (-d/m) = 1 := by
    rw [← Real.exp_add, show d/m + -d/m = 0 by ring, Real.exp_zero]
  apply le_of_eq
  symm
  calc
    _ = (Real.pi * gaussianPairPrefactor (v 0) (v 1) *
        (2*(b*Real.sqrt s)*(Real.sqrt (2*Real.pi*v (0 : Fin (n+1)).succ.succ))⁻¹)) *
        (Real.exp (d/m) * Real.exp (-d/m)) := by ring
    _ = _ := by rw [he, mul_one]

end

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.sphereTilted_smallBall_s2_oai := @OAI.CriticalSK.sphereTilted_smallBall_s2_oai
