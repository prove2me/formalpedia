-- Prove2me | solution 1 for OAI.AtomicTriangular.universal_energy_minimum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:39:37.414903+00:00
-- url     : https://prove2.me/submissions/72cf6ab1-ea33-4d70-a48e-5d4319c1d16a

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_TriangularEnergy
import Definitions.Def_OAIQ334E026
import Definitions.Def_OAIQ334E033
import Theorems.Thm_OAI_AtomicTriangular_gaussianPair_poisson_eu

section
-- module Solutions.OAIQ334_EU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Spectral
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.instDiscreteTopologySubtypePlaneMemSubmoduleIntTriangularModule _root_.OAI.TriangularUniversal.instIsZLatticeRealPlaneTriangularModule _root_.OAI.TriangularUniversal.nonzeroSite_countable _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/- Necessary analytic transfer from §2. We use finite positive measures for the
   comparison form; the eventual quadratic inequality also handles real signed
   linear combinations, without imposing spacing on the configuration. -/

lemma phase_continuous : Continuous (fun wx : Plane × Plane => phase wx.1 wx.2) := by
  unfold phase
  fun_prop

lemma phase_norm (w x : Plane) : ‖phase w x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma phase_sub (w x y : Plane) :
    phase w (x-y) = phase w x * conj (phase w y) := by
  simp only [phase, inner_sub_right, Complex.ofReal_mul, Complex.ofReal_sub,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  ring

lemma pattern_eq (μ : Measure Plane) (w : Plane) :
    pattern μ w = ∫ x, phase w x ∂μ := by
  simp only [pattern, charFun_apply, phase, inner_smul_right]
  congr 1
  funext x
  rw [real_inner_comm x w]

lemma pattern_continuous (μ : Measure Plane) [IsFiniteMeasure μ] :
    Continuous (pattern μ) := by
  unfold pattern
  fun_prop

lemma pattern_bound (μ : Measure Plane) (w : Plane) :
    ‖pattern μ w‖ ≤ μ.real Set.univ := norm_charFun_le _

lemma spectral_integrable (h : Plane → ℂ) (hh : Integrable h)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun w => h w * pattern μ w * conj (pattern ν w)) := by
  exact (hh.mul_bdd (pattern_continuous μ).aestronglyMeasurable
    (Eventually.of_forall (pattern_bound μ))).mul_bdd
    ((pattern_continuous ν).star.aestronglyMeasurable)
    (Eventually.of_forall fun w => by simpa using pattern_bound ν w)

lemma integral_phase_sub (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (w : Plane) :
    (∫ xy : Plane × Plane, phase w (xy.1 - xy.2) ∂(μ.prod ν)) =
      pattern μ w * conj (pattern ν w) := by
  simp_rw [phase_sub]
  rw [integral_prod_mul (phase w) (fun y => conj (phase w y)),
    integral_conj, ← pattern_eq, ← pattern_eq]

lemma kernelForm_spectral (f : Plane → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kernelForm f μ ν = ∫ w, 𝓕 f w * pattern μ w * conj (pattern ν w) := by
  have hm : AEStronglyMeasurable
      (fun p : (Plane × Plane) × Plane => phase p.2 (p.1.1 - p.1.2) * 𝓕 f p.2)
      ((μ.prod ν).prod volume) := by
    apply AEStronglyMeasurable.mul
    · exact (phase_continuous.comp (continuous_snd.prodMk
        (continuous_fst.fst.sub continuous_fst.snd))).aestronglyMeasurable
    · exact hF.aestronglyMeasurable.comp_snd
  have hint : Integrable
      (fun p : (Plane × Plane) × Plane => phase p.2 (p.1.1 - p.1.2) * 𝓕 f p.2)
      ((μ.prod ν).prod volume) := by
    apply (hF.norm.comp_snd (μ.prod ν)).mono' hm
    exact Eventually.of_forall fun p => by simp [phase_norm]
  have hp (x : Plane) : f x = ∫ w, phase w x * 𝓕 f w := by
    calc
      f x = 𝓕⁻ (𝓕 f) x := (congrFun (hc.fourierInv_fourier_eq hf hF) x).symm
      _ = _ := by rw [Real.fourierInv_eq']; rfl
  unfold kernelForm
  simp_rw [hp]
  rw [integral_integral_swap hint]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    dsimp only
    rw [integral_mul_const, integral_phase_sub]
    ring

lemma integral_reC {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  exact (integral_re hf).symm

lemma integral_sub_sub_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B C D : α → ℂ} (hA : Integrable A μ) (hB : Integrable B μ)
    (hC : Integrable C μ) (hD : Integrable D μ) :
    (∫ x, A x - B x - C x + D x ∂μ) =
      (∫ x, A x ∂μ) - (∫ x, B x ∂μ) - (∫ x, C x ∂μ) + ∫ x, D x ∂μ := by
  calc
    _ = (∫ x, A x - B x - C x ∂μ) + ∫ x, D x ∂μ := integral_add ((hA.sub hB).sub hC) hD
    _ = ((∫ x, A x - B x ∂μ) - ∫ x, C x ∂μ) + ∫ x, D x ∂μ := by
      exact congrArg (fun z => z + ∫ x, D x ∂μ) (integral_sub (hA.sub hB) hC)
    _ = _ := by rw [integral_sub hA hB]

lemma spectral_re_nonneg (z p : ℂ) (hz : z.im = 0) (hn : 0 ≤ z.re) :
    0 ≤ (z * p * conj p).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hz,
    zero_mul, sub_zero]
  nlinarith [sq_nonneg p.re, sq_nonneg p.im]

lemma kernelForm_comparison (f : Plane → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hreal : ∀ w, (𝓕 f w).im = 0) (hpos : ∀ w, 0 ≤ (𝓕 f w).re)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    2 * (kernelForm f μ ν).re - (kernelForm f ν ν).re ≤ (kernelForm f μ μ).re := by
  have hsym : (kernelForm f ν μ).re = (kernelForm f μ ν).re := by
    rw [kernelForm_spectral f hc hf hF, kernelForm_spectral f hc hf hF,
      integral_reC (spectral_integrable _ hF ν μ),
      integral_reC (spectral_integrable _ hF μ ν)]
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      hreal w, zero_mul, sub_zero]
    ring
  have hn : 0 ≤ (kernelForm f μ μ - kernelForm f μ ν - kernelForm f ν μ +
      kernelForm f ν ν).re := by
    simp only [kernelForm_spectral f hc hf hF]
    rw [← integral_sub_sub_add (spectral_integrable _ hF μ μ) (spectral_integrable _ hF μ ν)
      (spectral_integrable _ hF ν μ) (spectral_integrable _ hF ν ν)]
    have hh := integral_reC ((((spectral_integrable _ hF μ μ).sub (spectral_integrable _ hF μ ν)).sub
        (spectral_integrable _ hF ν μ)).add (spectral_integrable _ hF ν ν))
    simp only [Pi.add_apply, Pi.sub_apply] at hh
    rw [hh]
    apply integral_nonneg
    intro w
    change (0 : ℝ) ≤ (𝓕 f w * pattern μ w * conj (pattern μ w) -
        𝓕 f w * pattern μ w * conj (pattern ν w) -
        𝓕 f w * pattern ν w * conj (pattern μ w) +
        𝓕 f w * pattern ν w * conj (pattern ν w)).re
    have hp := spectral_re_nonneg (𝓕 f w) (pattern μ w - pattern ν w) (hreal w) (hpos w)
    have he : 𝓕 f w * pattern μ w * conj (pattern μ w) -
        𝓕 f w * pattern μ w * conj (pattern ν w) -
        𝓕 f w * pattern ν w * conj (pattern μ w) +
        𝓕 f w * pattern ν w * conj (pattern ν w) =
        𝓕 f w * (pattern μ w - pattern ν w) * conj (pattern μ w - pattern ν w) := by
      simp only [map_sub]
      ring
    rw [he]
    exact hp
  simp only [Complex.sub_re, Complex.add_re, hsym] at hn
  linarith
end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Cutoff
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.instDiscreteTopologySubtypePlaneMemSubmoduleIntTriangularModule _root_.OAI.TriangularUniversal.instIsZLatticeRealPlaneTriangularModule _root_.OAI.TriangularUniversal.nonzeroSite_countable _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal

lemma radialCutoff_nonneg (R T : ℝ) (x : Plane) : 0 ≤ radialCutoff R T x := le_max_left _ _
lemma radialCutoff_le_one (R T : ℝ) (x : Plane) : radialCutoff R T x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
lemma radialCutoff_continuous (R T : ℝ) : Continuous (radialCutoff R T) := by
  unfold radialCutoff
  fun_prop
lemma radialCutoff_eq_one {R T : ℝ} (hT : 0 < T) {x : Plane} (hx : ‖x‖ ≤ R) :
    radialCutoff R T x = 1 := by
  have h : 1 ≤ (R+T-‖x‖)/T := (le_div_iff₀ hT).mpr (by linarith)
  simp [radialCutoff, min_eq_left h]
lemma radialCutoff_eq_zero {R T : ℝ} (hT : 0 < T) {x : Plane} (hx : R+T ≤ ‖x‖) :
    radialCutoff R T x = 0 := by
  have h : (R+T-‖x‖)/T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
  exact max_eq_left ((min_le_right _ _).trans h)

lemma radialCutoff_compactSupport {R T : ℝ} (hT : 0 < T) :
    HasCompactSupport (radialCutoff R T) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) (R+T))
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (radialCutoff_eq_zero hT (le_of_not_ge h))

lemma radialCutoff_integrable {R T : ℝ} (hT : 0 < T) : Integrable (radialCutoff R T) :=
  (radialCutoff_continuous R T).integrable_of_hasCompactSupport (radialCutoff_compactSupport hT)

lemma clip_lipschitz : LipschitzWith 1 (fun x : ℝ => max 0 (min 1 x)) := by
  simpa using (LipschitzWith.const (0 : ℝ)).max
    ((LipschitzWith.const (1 : ℝ)).min LipschitzWith.id)

lemma radialCutoff_lipschitz {R T : ℝ} (hT : 0 < T) :
    LipschitzWith (T⁻¹).toNNReal (radialCutoff R T) := by
  have h : LipschitzWith (T⁻¹).toNNReal (fun x : Plane => (R+T-‖x‖)/T) := by
    apply LipschitzWith.of_dist_le'
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    calc
      |(R+T-‖x‖)/T - (R+T-‖y‖)/T| = |‖y‖-‖x‖|/T := by
        rw [← sub_div, abs_div, abs_of_pos hT]
        congr 2
        ring
      _ ≤ ‖x-y‖/T := by
        apply div_le_div_of_nonneg_right _ hT.le
        simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
      _ = T⁻¹ * ‖x-y‖ := by ring
  change LipschitzWith (T⁻¹).toNNReal (fun x : Plane => max 0 (min 1 ((R+T-‖x‖)/T)))
  simpa only [one_mul, Function.comp_def] using clip_lipschitz.comp h

lemma radialCutoff_sub_bound {R T : ℝ} (hT : 0 < T) (x z : Plane) :
    |radialCutoff R T (x-z) - radialCutoff R T x| ≤ ‖z‖/T := by
  have H := (radialCutoff_lipschitz (R := R) hT).norm_sub_le (x-z) x
  simpa [Real.norm_eq_abs, Real.coe_toNNReal _ (inv_nonneg.mpr hT.le),
    sub_sub_cancel_left, div_eq_mul_inv, mul_comm] using H

lemma plane_disk_volume {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Metric.closedBall (0 : Plane) R) = Real.pi * R^2 := by
  rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_two]
  simp [Real.pi_pos.le, hR, mul_comm]

lemma radialCutoff_integral_bound {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) :
    (∫ x, radialCutoff R T x) ≤ Real.pi*(R+T)^2 := by
  have hs := measurableSet_closedBall (x := (0 : Plane)) (ε := R+T)
  calc
    _ ≤ ∫ x, (Metric.closedBall (0 : Plane) (R+T)).indicator (fun _ => (1 : ℝ)) x := by
      apply integral_mono (radialCutoff_integrable hT)
        ((integrable_indicator_iff hs).mpr (integrableOn_const (by rw [EuclideanSpace.volume_closedBall_fin_two]; finiteness)))
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Plane) (R+T)
      · simpa [hx] using radialCutoff_le_one R T x
      · simp only [Set.indicator_of_notMem hx]
        have hx' : R+T ≤ ‖x‖ := le_of_lt (by
          simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
        rw [radialCutoff_eq_zero hT hx']
    _ = _ := by rw [integral_indicator_const 1 hs, smul_eq_mul, mul_one, plane_disk_volume (by linarith)]

lemma cutoffConvolution_integrable {f : Plane → ℂ} (hf : Integrable f)
    (R T : ℝ) (x : Plane) :
    Integrable (fun z => radialCutoff R T (x-z) • f z) := by
  exact hf.bdd_smul 1 ((radialCutoff_continuous R T).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg R T (x-z))]
        using radialCutoff_le_one R T (x-z))

lemma cutoffConvolution_error {f : Plane → ℂ} (hf : Integrable f)
    (hm : Integrable (fun z => ‖z‖ * ‖f z‖))
    {R T : ℝ} (hT : 0 < T) (x : Plane) :
    ‖cutoffConvolution f R T x - radialCutoff R T x • (∫ z, f z)‖ ≤ firstMoment f / T := by
  have hi2 : Integrable (fun z => radialCutoff R T x • f z) := by
    simpa only [Pi.smul_def] using hf.smul (radialCutoff R T x)
  have hi := (cutoffConvolution_integrable hf R T x).sub hi2
  have he : cutoffConvolution f R T x - radialCutoff R T x • (∫ z, f z) =
      ∫ z, (radialCutoff R T (x-z) - radialCutoff R T x) • f z := by
    simp_rw [sub_smul]
    rw [integral_sub (cutoffConvolution_integrable hf R T x)
      hi2, integral_smul]
    rfl
  rw [he]
  calc
    _ ≤ ∫ z, ‖(radialCutoff R T (x-z) - radialCutoff R T x) • f z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (‖z‖ * ‖f z‖) / T := by
      apply integral_mono
      · simpa only [sub_smul, Pi.sub_apply] using hi.norm
      · exact hm.div_const T
      · intro z
        dsimp only
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ (‖z‖ / T) * ‖f z‖ := mul_le_mul_of_nonneg_right
            (radialCutoff_sub_bound hT x z) (norm_nonneg _)
          _ = _ := by ring
    _ = _ := by rw [integral_div]; rfl

lemma cutoffConvolution_re_bounds {f : Plane → ℂ} (hf : Integrable f)
    (hm : Integrable (fun z => ‖z‖ * ‖f z‖))
    {R T : ℝ} (hT : 0 < T) (x : Plane) :
    radialCutoff R T x * (∫ z, f z).re - firstMoment f / T ≤
      (cutoffConvolution f R T x).re ∧
    (cutoffConvolution f R T x).re ≤
      radialCutoff R T x * (∫ z, f z).re + firstMoment f / T := by
  have h := (Complex.abs_re_le_norm _).trans (cutoffConvolution_error hf hm (R := R) hT x)
  rw [Complex.sub_re, Complex.real_smul, Complex.mul_re] at h
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  constructor <;> linarith [abs_le.mp h]



lemma cutoffMeasure_finite {R T : ℝ} (hT : 0 < T) : IsFiniteMeasure (cutoffMeasure R T) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (radialCutoff_integrable hT)
    (Eventually.of_forall (radialCutoff_nonneg R T))]
  exact ENNReal.ofReal_ne_top

lemma integral_cutoffMeasure (R T : ℝ) (f : Plane → ℂ) :
    (∫ x, f x ∂cutoffMeasure R T) = ∫ x, radialCutoff R T x • f x := by
  rw [cutoffMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (radialCutoff_nonneg _ _ _)]
  · exact (radialCutoff_continuous R T).measurable.ennreal_ofReal
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

lemma cutoffMeasure_mass {R T : ℝ} (hT : 0 < T) :
    (cutoffMeasure R T).real Set.univ = ∫ x, radialCutoff R T x := by
  rw [measureReal_def, cutoffMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal (radialCutoff_integrable hT)
      (Eventually.of_forall (radialCutoff_nonneg R T)), ENNReal.toReal_ofReal]
  exact integral_nonneg (radialCutoff_nonneg R T)

lemma cutoffConvolution_eq_integral (f : Plane → ℂ) (R T : ℝ) (x : Plane) :
    cutoffConvolution f R T x = ∫ y, f (x-y) ∂cutoffMeasure R T := by
  rw [integral_cutoffMeasure]
  have h := integral_sub_left_eq_self (fun y => radialCutoff R T y • f (x-y)) volume x
  simpa only [sub_sub_cancel, cutoffConvolution] using h
end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Density
attribute [-instance] _root_.OAI.TriangularUniversal.instDiscreteTopologySubtypePlaneMemSubmoduleIntTriangularModule _root_.OAI.TriangularUniversal.instIsZLatticeRealPlaneTriangularModule _root_.OAI.TriangularUniversal.nonzeroSite_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal

lemma regular_kernel_integrable (f : LPFunction)
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun xy : Plane × Plane => f (xy.1-xy.2)) (μ.prod ν) := by
  exact (integrable_const f.bound).mono'
    (f.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    (Eventually.of_forall fun xy => f.norm_bound (xy.1-xy.2))

lemma regular_firstMoment_integrable (f : LPFunction) :
    Integrable (fun z => ‖z‖ * ‖f z‖) := f.momentIntegrable

lemma firstMoment_nonneg (f : Plane → ℂ) : 0 ≤ firstMoment f :=
  integral_nonneg fun z => mul_nonneg (norm_nonneg z) (norm_nonneg (f z))

lemma kernelForm_cutoff (f : LPFunction) {R T : ℝ} (hT : 0 < T)
    (μ : Measure Plane) [IsFiniteMeasure μ] :
    kernelForm f μ (cutoffMeasure R T) = ∫ x, cutoffConvolution f R T x ∂μ := by
  let := cutoffMeasure_finite (R := R) hT
  rw [kernelForm, integral_prod _ (regular_kernel_integrable f μ (cutoffMeasure R T))]
  simp_rw [cutoffConvolution_eq_integral]

lemma kernelForm_cutoff_self_upper (f : LPFunction)
    (ha : 0 ≤ (∫ z, f z).re) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T) :
    (kernelForm f (cutoffMeasure R T) (cutoffMeasure R T)).re ≤
      ((∫ z, f z).re + firstMoment f / T) * Real.pi * (R+T)^2 := by
  let := cutoffMeasure_finite (R := R) hT
  have hi : Integrable (fun x => cutoffConvolution f R T x) (cutoffMeasure R T) := by
    simpa only [cutoffConvolution_eq_integral] using
      (regular_kernel_integrable f (cutoffMeasure R T) (cutoffMeasure R T)).integral_prod_left
  rw [kernelForm_cutoff f hT, integral_reC hi]
  calc
    _ ≤ ∫ _ : Plane, ((∫ z, f z).re + firstMoment f / T) ∂cutoffMeasure R T := by
      apply integral_mono hi.re (integrable_const _)
      intro x
      change (cutoffConvolution f R T x).re ≤
        (∫ z, f z).re + firstMoment f / T
      have hb := (cutoffConvolution_re_bounds f.integrable
        (regular_firstMoment_integrable f) (R := R) hT x).2
      have hm := mul_le_mul_of_nonneg_right (radialCutoff_le_one R T x) ha
      linarith
    _ = ((∫ z, f z).re + firstMoment f / T) * (∫ x, radialCutoff R T x) := by
      rw [integral_const, smul_eq_mul, cutoffMeasure_mass hT]; ring
    _ ≤ ((∫ z, f z).re + firstMoment f / T) * (Real.pi*(R+T)^2) := by
      gcongr
      · exact add_nonneg ha (div_nonneg (firstMoment_nonneg f) hT.le)
      · exact radialCutoff_integral_bound hR hT
    _ = _ := by ring


lemma integral_pointsMeasure (S : Finset Plane) (f : Plane → ℂ) :
    (∫ x, f x ∂pointsMeasure S) = ∑ x ∈ S, f x := by
  rw [pointsMeasure, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i hi
    exact integrable_dirac (by finiteness)

lemma kernelForm_points_points (f : LPFunction) (S : Finset Plane) :
    kernelForm f (pointsMeasure S) (pointsMeasure S) =
      ∑ x ∈ S, ∑ y ∈ S, f (x-y) := by
  rw [kernelForm, integral_prod _ (regular_kernel_integrable f _ _), integral_pointsMeasure]
  simp only [integral_pointsMeasure]

lemma kernelForm_points_cutoff_lower (f : LPFunction)
    (S : Finset Plane) {R T : ℝ} (hT : 0 < T) (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    (S.card : ℝ) * ((∫ z, f z).re - firstMoment f / T) ≤
      (kernelForm f (pointsMeasure S) (cutoffMeasure R T)).re := by
  rw [kernelForm_cutoff f hT, integral_pointsMeasure, Complex.re_sum]
  calc
    _ = ∑ _x ∈ S, ((∫ z, f z).re - firstMoment f / T) := by simp <;> ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      have h := (cutoffConvolution_re_bounds f.integrable
        (regular_firstMoment_integrable f) (R := R) hT x).1
      rwa [radialCutoff_eq_one hT (hS x hx), one_mul] at h

lemma fourier_zero_eq_integral (f : Plane → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [Real.fourier_eq]
  simp

/-- The exact finite-disk estimate underlying the density-only bound.
The correction uses a cutoff of thickness T and its first moment, never a
uniform spacing or local-count bound on S. -/
lemma finite_disk_lp (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (S : Finset Plane) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T)
    (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    2*(S.card : ℝ)*((∫ z, f z).re - firstMoment f/T) -
      ((∫ z, f z).re + firstMoment f/T)*Real.pi*(R+T)^2 ≤
      ∑ x ∈ S, ∑ y ∈ S, (f (x-y)).re := by
  let := cutoffMeasure_finite (R := R) hT
  have ha : 0 ≤ (∫ z, f z).re := by simpa only [fourier_zero_eq_integral] using hpos 0
  have hc := kernelForm_comparison f f.continuous f.integrable
    f.fourierIntegrable hreal hpos (pointsMeasure S) (cutoffMeasure R T)
  have hl := kernelForm_points_cutoff_lower f S hT hS
  have hu := kernelForm_cutoff_self_upper f ha hR hT
  rw [kernelForm_points_points] at hc
  simp only [Complex.re_sum] at hc
  nlinarith

lemma ofReal_finset_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ x ∈ S, f x) ≤ ∑ x ∈ S, ENNReal.ofReal (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    simp only [Finset.sum_insert hx]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

lemma offdiag_sum_eq (f : Plane → ℝ) (S : Finset Plane) :
    (∑ x ∈ S, ∑ y ∈ S.erase x, f (x-y)) =
      (∑ x ∈ S, ∑ y ∈ S, f (x-y)) - (S.card : ℝ)*f 0 := by
  have he : (∑ x ∈ S, ∑ y ∈ S.erase x, f (x-y)) + (S.card : ℝ)*f 0 =
      ∑ x ∈ S, ∑ y ∈ S, f (x-y) := by
    calc
      _ = ∑ x ∈ S, ((∑ y ∈ S.erase x, f (x-y)) + f 0) := by
        rw [Finset.sum_add_distrib]; simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        simpa only [sub_self] using Finset.sum_erase_add S (fun y => f (x-y)) hx
  linarith

lemma normalized_offdiag_minorization (f : Plane → ℂ) (g : ℝ → ℝ)
    (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    (S : Finset Plane) (hN : 0 < S.card) :
    ENNReal.ofReal ((∑ x ∈ S, ∑ y ∈ S.erase x, (f (x-y)).re)/(S.card : ℝ)) ≤
      (S.card : ℝ≥0∞)⁻¹ * ∑ x ∈ S, ∑ y ∈ S.erase x, ENNReal.ofReal (g (‖x-y‖^2)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    div_eq_mul_inv, mul_comm]
  gcongr
  calc
    _ ≤ ∑ x ∈ S, ENNReal.ofReal (∑ y ∈ S.erase x, (f (x-y)).re) := ofReal_finset_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      calc
        _ ≤ ∑ y ∈ S.erase x, ENNReal.ofReal ((f (x-y)).re) := ofReal_finset_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro y hy
          apply ENNReal.ofReal_le_ofReal
          apply hminor
          exact sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hy).1)

lemma finite_disk_energy_lp (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (g : ℝ → ℝ) (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    (C : Set Plane) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T)
    (hN : 0 < diskCount C R) :
    ENNReal.ofReal (2*((∫ z, f z).re - firstMoment f/T) -
      ((∫ z, f z).re + firstMoment f/T) * (Real.pi*(R+T)^2/(diskCount C R : ℝ)) -
        (f 0).re) ≤ diskEnergy g C R := by
  have hS : ∀ x ∈ diskPoints C R, ‖x‖ ≤ R := by
    intro x hx
    unfold diskPoints at hx
    split_ifs at hx with h
    · simpa only [Metric.mem_closedBall, dist_zero_right] using (h.mem_toFinset.mp hx).2
    · simp at hx
  have hl := finite_disk_lp f hreal hpos (diskPoints C R) hR hT hS
  have hN' : (0 : ℝ) < diskCount C R := by exact_mod_cast hN
  have he : 2*((∫ z, f z).re - firstMoment f/T) -
      ((∫ z, f z).re + firstMoment f/T)*(Real.pi*(R+T)^2/(diskCount C R : ℝ)) -
        (f 0).re ≤
      (∑ x ∈ diskPoints C R, ∑ y ∈ (diskPoints C R).erase x, (f (x-y)).re) /
        (diskCount C R : ℝ) := by
    rw [le_div_iff₀ hN', offdiag_sum_eq (fun z => (f z).re)]
    change _ ≤ _ - (diskCount C R : ℝ)*(f 0).re
    have hN0 : (diskCount C R : ℝ) ≠ 0 := ne_of_gt hN'
    have hid : (2*((∫ z, f z).re - firstMoment f/T) -
        ((∫ z, f z).re + firstMoment f/T)*(Real.pi*(R+T)^2/(diskCount C R : ℝ)) -
        (f 0).re) * (diskCount C R : ℝ) =
        2*(diskCount C R : ℝ)*((∫ z, f z).re - firstMoment f/T) -
        ((∫ z, f z).re + firstMoment f/T)*Real.pi*(R+T)^2 -
        (diskCount C R : ℝ)*(f 0).re := by
      field_simp [hN0]
    rw [hid]
    exact sub_le_sub_right hl _
  exact (ENNReal.ofReal_le_ofReal he).trans
    (normalized_offdiag_minorization f g hminor (diskPoints C R) hN)

lemma density_count_eventually_pos {C : Set Plane} (hD : DensityOne C) :
    ∀ᶠ R : ℝ in atTop, 0 < diskCount C R := by
  have hp := hD.eventually (lt_mem_nhds (show (1/2 : ℝ) < 1 by norm_num))
  filter_upwards [hp, eventually_gt_atTop (0 : ℝ)] with R h hR
  have hden : 0 < Real.pi * R^2 := mul_pos Real.pi_pos (sq_pos_of_pos hR)
  have hn := (lt_div_iff₀ hden).mp h
  have hpR : (0 : ℝ) < diskCount C R := by nlinarith
  exact_mod_cast hpR

lemma density_volume_ratio {C : Set Plane} (hD : DensityOne C) (ε : ℝ) :
    Tendsto (fun R : ℝ => Real.pi*(R+ε*R)^2/(diskCount C R : ℝ))
      atTop (𝓝 ((1+ε)^2)) := by
  have h := (hD.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)).const_mul ((1+ε)^2)
  convert h using 1
  · ext R
    simp only [inv_div]
    ring
  · simp

lemma density_lp_epsilon (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (g : ℝ → ℝ) (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    {C : Set Plane} (hD : DensityOne C) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (2*(∫ z, f z).re - (∫ z, f z).re*(1+ε)^2 - (f 0).re) ≤ energy g C := by
  have hm : Tendsto (fun R : ℝ => firstMoment f/(ε*R)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hε)
  have ha : Tendsto (fun _ : ℝ => (∫ z, f z).re) atTop (𝓝 (∫ z, f z).re) := tendsto_const_nhds
  have hL : Tendsto (fun R : ℝ =>
      2*((∫ z, f z).re-firstMoment f/(ε*R)) -
      ((∫ z, f z).re+firstMoment f/(ε*R))*(Real.pi*(R+ε*R)^2/(diskCount C R : ℝ)) -
      (f 0).re) atTop
      (𝓝 (2*(∫ z, f z).re - (∫ z, f z).re*(1+ε)^2 - (f 0).re)) := by
    simpa only [sub_zero, add_zero] using
      (((ha.sub hm).const_mul 2).sub ((ha.add hm).mul (density_volume_ratio hD ε))).sub_const (f 0).re
  have hLe := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL
  change _ ≤ Filter.liminf (diskEnergy g C) atTop
  rw [← hLe.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [density_count_eventually_pos hD, eventually_gt_atTop (0 : ℝ)] with R hN hR
  exact finite_disk_energy_lp f hreal hpos g hminor C hR.le (mul_pos hε hR) hN

/-- Source §2, density-only linear programming bound, for the exact ordered-pair
centered-disk ENNReal liminf. This requires no uniform separation, special
local-count bound, finite energy, or decay of the potential. -/
lemma density_lp (f : LPFunction)
    (hreal : ∀ w, (𝓕 (f : Plane → ℂ) w).im = 0)
    (hpos : ∀ w, 0 ≤ (𝓕 (f : Plane → ℂ) w).re)
    (g : ℝ → ℝ) (hminor : ∀ x : Plane, x ≠ 0 → (f x).re ≤ g (‖x‖^2))
    {C : Set Plane} (hD : DensityOne C) :
    ENNReal.ofReal ((∫ z, f z).re - (f 0).re) ≤ energy g C := by
  let a := (∫ z, f z).re
  let b := (f 0).re
  have hc : Continuous (fun ε : ℝ => 2*a-a*(1+ε)^2-b) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => 2*a-a*(1+ε)^2-b) (𝓝[>] (0 : ℝ)) (𝓝 (a-b)) := by
    convert (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  apply le_of_tendsto he
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact density_lp_epsilon f hreal hpos g hminor hD hε

end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Mixtures
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal

lemma triangularPoint_norm_sq (j k : ℤ) :
    b * ‖triangularPoint (j, k)‖ ^ 2 = (j : ℝ) ^ 2 + (j : ℝ) * (k : ℝ) + (k : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one, Real.norm_eq_abs,
    sq_abs, mul_pow]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (2 / Real.sqrt (3 : ℝ))) ^ 2 = 2 / Real.sqrt 3 :=
    Real.sq_sqrt (by positivity)
  rw [hc]
  dsimp [b]
  field_simp
  nlinarith [hs]

lemma triangularPoint_sub (j k : ℤ × ℤ) :
    triangularPoint (j - k) = triangularPoint j - triangularPoint k := by
  ext i
  fin_cases i <;> simp [triangularPoint] <;> ring

lemma triangularLattice_sub {x y : Plane} (hx : x ∈ triangularLattice)
    (hy : y ∈ triangularLattice) : x - y ∈ triangularLattice := by
  rcases hx with ⟨j, rfl⟩
  rcases hy with ⟨k, rfl⟩
  exact ⟨j - k, triangularPoint_sub j k⟩

lemma diskPoints_subset (C : Set Plane) (R : ℝ) :
    (diskPoints C R : Set Plane) ⊆ C := by
  intro x hx
  unfold diskPoints at hx
  split_ifs at hx with h
  · exact (h.mem_toFinset.mp hx).1
  · simp at hx

lemma finite_lattice_row_le (g : ℝ → ℝ) (s : Finset Plane)
    (hs : (s : Set Plane) ⊆ triangularLattice) (x : Plane)
    (hx : x ∈ triangularLattice) :
    ∑ y ∈ s.erase x, ENNReal.ofReal (g (‖x - y‖ ^ 2)) ≤ latticeEnergy g := by
  let f : {y : Plane // y ∈ s.erase x} →
      {a : Plane // a ∈ triangularLattice ∧ a ≠ 0} :=
    fun y => ⟨x - y.val, triangularLattice_sub hx (hs (Finset.mem_of_mem_erase y.property)),
      sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase y.property))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have H := congrArg Subtype.val h
    dsimp [f] at H
    exact sub_right_injective H
  have H := ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun a : {a : Plane // a ∈ triangularLattice ∧ a ≠ 0} =>
      ENNReal.ofReal (g (‖a.val‖ ^ 2)))
  change (∑' y : (s.erase x), ENNReal.ofReal (g (‖x - (y : Plane)‖ ^ 2))) ≤
    latticeEnergy g at H
  rw [tsum_fintype] at H
  have he := Finset.sum_subtype (F := inferInstance) (s.erase x) (fun _ => Iff.rfl)
    (fun y : Plane => ENNReal.ofReal (g (‖x - y‖ ^ 2)))
  exact he ▸ H

lemma lattice_disk_energy_le (g : ℝ → ℝ) (R : ℝ) :
    diskEnergy g triangularLattice R ≤ latticeEnergy g := by
  let s := diskPoints triangularLattice R
  have hs : (s : Set Plane) ⊆ triangularLattice := diskPoints_subset _ _
  by_cases hn : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hn
    change (s.card : ℝ≥0∞)⁻¹ * (∑ x ∈ s, ∑ y ∈ s.erase x,
      ENNReal.ofReal (g (‖x - y‖ ^ 2))) ≤ _
    simp [he]
  have hn' : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn
  have H : (∑ x ∈ s, ∑ y ∈ s.erase x, ENNReal.ofReal (g (‖x - y‖ ^ 2))) ≤
      (s.card : ℝ≥0∞) * latticeEnergy g := by
    calc
      _ ≤ ∑ x ∈ s, latticeEnergy g := Finset.sum_le_sum fun x hx =>
        finite_lattice_row_le g s hs x (hs hx)
      _ = _ := by simp
  change (s.card : ℝ≥0∞)⁻¹ * _ ≤ _
  calc
    _ ≤ (s.card : ℝ≥0∞)⁻¹ * ((s.card : ℝ≥0∞) * latticeEnergy g) :=
      mul_le_mul_of_nonneg_left H zero_le
    _ = latticeEnergy g := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hn' (by simp), one_mul]

lemma lattice_energy_upper (g : ℝ → ℝ) :
    energy g triangularLattice ≤ latticeEnergy g := by
  apply Filter.liminf_le_of_frequently_le'
  exact Filter.Eventually.frequently (Filter.Eventually.of_forall (lattice_disk_energy_le g))

lemma triangularPoint_equiv (j k : ℤ) :
    triangularPoint (j, k) = triangularEquiv ![(j : ℝ), (k : ℝ)] := rfl

lemma triangularModule_coe : (triangularModule : Set Plane) = triangularLattice := by
  ext x
  change x ∈ Submodule.span ℤ (Set.range triangularBasis) ↔ _
  rw [triangularBasis.mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h
    rcases h 0 with ⟨j, hj⟩
    rcases h 1 with ⟨k, hk⟩
    refine ⟨(j, k), ?_⟩
    apply triangularEquiv.symm.injective
    rw [triangularPoint_equiv, LinearEquiv.symm_apply_apply]
    ext i
    fin_cases i
    · exact hj
    · exact hk
  · rintro ⟨⟨j, k⟩, rfl⟩ i
    fin_cases i
    · refine ⟨j, ?_⟩
      change (j : ℝ) = (triangularEquiv.symm (triangularPoint (j, k))) 0
      rw [triangularPoint_equiv, LinearEquiv.symm_apply_apply]
      rfl
    · refine ⟨k, ?_⟩
      change (k : ℝ) = (triangularEquiv.symm (triangularPoint (j, k))) 1
      rw [triangularPoint_equiv, LinearEquiv.symm_apply_apply]
      rfl

lemma triangular_locallyFinite : LocallyFinite triangularLattice := by
  intro R
  rw [← triangularModule_coe, Set.inter_comm]
  exact ZSpan.setFinite_inter triangularBasis Metric.isBounded_closedBall

lemma triangularBasis_apply (i : Fin 2) :
    triangularBasis i = triangularEquiv (Pi.single i 1) := by
  simp [triangularBasis, Module.Basis.coe_ofEquivFun]

lemma triangular_det :
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.det triangularBasis = 1 := by
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, triangularBasis_apply]
  simp only [triangularEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  have hs := Real.sq_sqrt (le_of_lt (show 0 < 2 / Real.sqrt 3 from div_pos (by norm_num) sqrt_three_pos))
  generalize Real.sqrt (2 / Real.sqrt 3) = a at hs ⊢
  simp
  field_simp [ne_of_gt sqrt_three_pos] at hs ⊢
  nlinarith

lemma triangular_covolume : ZLattice.covolume triangularModule = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain triangularModule
    MeasureTheory.volume (ZSpan.isAddFundamentalDomain triangularBasis MeasureTheory.volume)]
  rw [ZSpan.measureReal_fundamentalDomain triangularBasis MeasureTheory.volume
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, triangular_det, abs_one, one_mul]
  rw [MeasureTheory.measureReal_def, MeasureTheory.measure_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis MeasureTheory.volume)]
  change (MeasureTheory.volume (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ))).toReal = 1
  rw [OrthonormalBasis.volume_parallelepiped, ENNReal.toReal_one]

lemma diskCount_eq_card (C : Set Plane) (hC : LocallyFinite C) (R : ℝ) :
    diskCount C R = Nat.card (C ∩ Metric.closedBall (0 : Plane) R : Set Plane) := by
  unfold diskCount diskPoints
  rw [dite_eq_left (hC R)]
  exact (Set.ncard_eq_toFinset_card _ (hC R)).symm

lemma norm_square_sublevel (R : ℝ) (hR : 0 ≤ R) :
    {x : Plane | x ∈ (Set.univ : Set Plane) ∧ ‖x‖ ^ 2 ≤ R ^ 2} =
      Metric.closedBall (0 : Plane) R := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and, Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg x]

lemma triangular_count_asymptotic :
    Tendsto (fun R : ℝ => (diskCount triangularLattice R : ℝ) / R ^ 2)
      atTop (𝓝 Real.pi) := by
  have hunit : {x : Plane | x ∈ (Set.univ : Set Plane) ∧ ‖x‖ ^ 2 ≤ 1} =
      Metric.closedBall (0 : Plane) 1 := by
    simpa only [one_pow] using norm_square_sublevel 1 zero_le_one
  have H := ZLattice.covolume.tendsto_card_le_div' triangularModule
    (X := Set.univ) (F := fun x => ‖x‖ ^ 2)
    (fun _ _ _ _ => Set.mem_univ _)
    (by
      intro x r hr
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, mul_pow,
        finrank_euclideanSpace, Fintype.card_fin])
    (by rw [hunit]; exact Metric.isBounded_closedBall)
    (by rw [hunit]; exact Metric.isClosed_closedBall.measurableSet)
    (by
      rw [hunit, frontier_closedBall (0 : Plane) one_ne_zero]
      exact MeasureTheory.Measure.addHaar_sphere MeasureTheory.volume _ _)
  have hvol : MeasureTheory.volume.real (Metric.closedBall (0 : Plane) 1) = Real.pi := by
    rw [MeasureTheory.measureReal_def, EuclideanSpace.volume_closedBall_fin_two]
    simp [Real.pi_pos.le]
  rw [hunit, hvol, triangular_covolume, div_one] at H
  apply (H.comp (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  dsimp
  rw [norm_square_sublevel R hR, diskCount_eq_card _ triangular_locallyFinite,
    ← triangularModule_coe, Set.inter_comm]
  rfl

lemma mem_diskPoints_iff (C : Set Plane) (hC : LocallyFinite C) (R : ℝ) (x : Plane) :
    x ∈ diskPoints C R ↔ x ∈ C ∧ ‖x‖ ≤ R := by
  simp [diskPoints, hC R, Metric.mem_closedBall, dist_zero_right]

lemma triangular_count_pos {R : ℝ} (hR : 0 ≤ R) : 0 < diskCount triangularLattice R := by
  apply Finset.card_pos.mpr
  refine ⟨0, (mem_diskPoints_iff _ triangular_locallyFinite _ _).mpr ?_⟩
  exact ⟨⟨(0, 0), triangularPoint_zero⟩, by simpa using hR⟩

lemma lattice_interior_count_ratio (M : ℝ) :
    Tendsto (fun R : ℝ => (diskCount triangularLattice (R - M) : ℝ) /
      (diskCount triangularLattice R : ℝ)) atTop (𝓝 1) := by
  have hshift : Tendsto (fun R : ℝ => R - M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + M)] with R hR
    linarith
  have hrat : Tendsto (fun R : ℝ => (R - M) / R) atTop (𝓝 1) := by
    have H := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_id.const_div_atTop M)
    simp only [sub_zero] at H
    apply H.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    dsimp only [id]
    field_simp [ne_of_gt hR]
  have H := ((triangular_count_asymptotic.comp hshift).mul (hrat.pow 2)).div
    triangular_count_asymptotic Real.pi_ne_zero
  simp only [one_pow, mul_one, div_self Real.pi_ne_zero] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (|M| + 1)] with R hR
  have hR0 : 0 < R := by linarith [abs_nonneg M]
  have hRM : 0 < R - M := by linarith [le_abs_self M]
  have hc : (diskCount triangularLattice R : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (triangular_count_pos hR0.le)
  dsimp
  field_simp [ne_of_gt hR0, ne_of_gt hRM, hc]

lemma lattice_interior_count_ratio_ennreal (M : ℝ) :
    Tendsto (fun R : ℝ => (diskCount triangularLattice R : ℝ≥0∞)⁻¹ *
      (diskCount triangularLattice (R - M) : ℝ≥0∞)) atTop (𝓝 1) := by
  have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (lattice_interior_count_ratio M)
  rw [ENNReal.ofReal_one] at H
  apply H.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  have hc : 0 < (diskCount triangularLattice R : ℝ) := by
    exact_mod_cast triangular_count_pos hR
  dsimp only [Function.comp_apply]
  rw [ENNReal.ofReal_div_of_pos hc]
  simp only [ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

lemma finite_lattice_row_ge (g : ℝ → ℝ) (F : Finset NonzeroSite) (M : ℝ)
    (hM : ∀ a ∈ F, ‖a.val‖ ≤ M) (R : ℝ) (x : Plane)
    (hx : x ∈ diskPoints triangularLattice (R - M)) :
    ∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2)) ≤
      ∑ y ∈ (diskPoints triangularLattice R).erase x,
        ENNReal.ofReal (g (‖x - y‖ ^ 2)) := by
  have hx' := (mem_diskPoints_iff _ triangular_locallyFinite _ _).mp hx
  have hinj : Function.Injective (fun a : NonzeroSite => x - a.val) := by
    intro a b h
    exact Subtype.ext (sub_right_injective h)
  have hsub : F.image (fun a : NonzeroSite => x - a.val) ⊆
      (diskPoints triangularLattice R).erase x := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have : a.val = 0 := by exact sub_eq_self.mp he
      exact a.property.2 this
    · apply (mem_diskPoints_iff _ triangular_locallyFinite _ _).mpr
      refine ⟨triangularLattice_sub hx'.1 a.property.1, ?_⟩
      have := norm_sub_le x a.val
      linarith [hx'.2, hM a ha]
  calc
    _ = ∑ a ∈ F, ENNReal.ofReal (g (‖x - (x - a.val)‖ ^ 2)) := by simp
    _ = ∑ y ∈ F.image (fun a : NonzeroSite => x - a.val),
        ENNReal.ofReal (g (‖x - y‖ ^ 2)) := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

lemma finite_lattice_disk_energy_ge (g : ℝ → ℝ) (F : Finset NonzeroSite) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ a ∈ F, ‖a.val‖ ≤ M) (R : ℝ) :
    ((diskCount triangularLattice R : ℝ≥0∞)⁻¹ *
      (diskCount triangularLattice (R - M) : ℝ≥0∞)) *
      (∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) ≤
      diskEnergy g triangularLattice R := by
  have hsub : diskPoints triangularLattice (R - M) ⊆ diskPoints triangularLattice R := by
    intro x hx
    rw [mem_diskPoints_iff _ triangular_locallyFinite] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have H : (diskCount triangularLattice (R - M) : ℝ≥0∞) *
      (∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) ≤
      ∑ x ∈ diskPoints triangularLattice R,
        ∑ y ∈ (diskPoints triangularLattice R).erase x,
          ENNReal.ofReal (g (‖x - y‖ ^ 2)) := by
    calc
      _ = ∑ x ∈ diskPoints triangularLattice (R - M),
          (∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) := by simp [diskCount]
      _ ≤ ∑ x ∈ diskPoints triangularLattice (R - M),
          ∑ y ∈ (diskPoints triangularLattice R).erase x,
            ENNReal.ofReal (g (‖x - y‖ ^ 2)) :=
        Finset.sum_le_sum fun x hx => finite_lattice_row_ge g F M hM R x hx
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left H zero_le

lemma lattice_energy_lower (g : ℝ → ℝ) :
    latticeEnergy g ≤ energy g triangularLattice := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro F
  let M : ℝ := ∑ a ∈ F, ‖a.val‖
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hM : ∀ a ∈ F, ‖a.val‖ ≤ M := fun a ha =>
    Finset.single_le_sum (fun i _ => norm_nonneg i.val) ha
  have H := ENNReal.Tendsto.mul_const (lattice_interior_count_ratio_ennreal M)
    (b := ∑ a ∈ F, ENNReal.ofReal (g (‖a.val‖ ^ 2))) (Or.inl one_ne_zero)
  simp only [one_mul] at H
  rw [← H.liminf_eq]
  exact liminf_le_liminf (Filter.Eventually.of_forall
    (finite_lattice_disk_energy_ge g F M hM0 hM))

lemma lattice_energy_eq (g : ℝ → ℝ) :
    latticeEnergy g = energy g triangularLattice :=
  le_antisymm (lattice_energy_lower g) (lattice_energy_upper g)

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
noncomputable section
namespace TriangularUniversal.PositiveMixture

lemma moment_difference (m : ℕ → ℝ) (r j : ℕ) :
    momentFunctional m (Polynomial.X^j*(1-Polynomial.X)^r) = difference m r j := by
  induction r generalizing j with
  | zero => simp [difference]
  | succ r ih =>
    rw [show (Polynomial.X^j*(1-Polynomial.X)^(r+1) : ℝ[X]) =
      Polynomial.X^j*(1-Polynomial.X)^r-Polynomial.X^(j+1)*(1-Polynomial.X)^r by ring]
    rw [map_sub, ih, ih, difference]

@[simp] lemma moment_bernstein (m : ℕ → ℝ) (n p : ℕ) :
    momentFunctional m (bernsteinPolynomial ℝ n p) =
      (n.choose p : ℝ)*difference m (n-p) p := by
  rw [bernsteinPolynomial, mul_assoc]
  rw [show (n.choose p : ℝ[X]) = Polynomial.C (n.choose p : ℝ) by simp]
  rw [← Polynomial.smul_eq_C_mul, map_smul, moment_difference]
  rfl

lemma weight_nonneg {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n p : ℕ) :
    0 ≤ weight m n p := mul_nonneg (Nat.cast_nonneg _) (hm _ _)

lemma weight_sum (m : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range (n+1), weight m n p = m 0 := by
  simp_rw [weight, ← moment_bernstein]
  rw [← map_sum, bernsteinPolynomial.sum]
  simpa using moment_pow m 0

lemma bernsteinBasis_sum (n : ℕ) (x : ℝ) :
    ∑ d ∈ range (n+1), bernsteinBasis n d x = 1 := by
  calc
    _ = (x+(1-x))^n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [bernsteinBasis]
      ring
    _ = 1 := by simp

lemma choose_ratio (n r d : ℕ) (hr : r ≤ n) (hd : r ≤ d) :
    (d.choose r : ℝ)/(n.choose r : ℝ)*(n.choose d : ℝ) =
      ((n-r).choose (d-r) : ℝ) := by
  have h : (n.choose d : ℝ)*(d.choose r : ℝ) =
      (n.choose r : ℝ)*((n-r).choose (d-r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n:=n) hd
  have hn : (n.choose r : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hr
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff hn).mpr
  first | (convert h using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (h.trans (le_of_eq (by ring)))

lemma bernstein_monomial (n r : ℕ) (hr : r ≤ n) (x : ℝ) :
    ∑ d ∈ range (n+1), ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x = x^r := by
  let f : ℕ → ℝ := fun d => ((d.choose r : ℝ)/(n.choose r : ℝ))*bernsteinBasis n d x
  have hlo : ∑ d ∈ range r, f d = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    simp [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hd)]
  have heq : ∀ d, r ≤ d →
      f d = x^r * ((n-r).choose (d-r) : ℝ)*x^(d-r)*(1-x)^((n-r)-(d-r)) := by
    intro d hd
    dsimp [f,bernsteinBasis]
    rw [show n-d = (n-r)-(d-r) by omega]
    rw [show d = r+(d-r) by omega, pow_add]
    have hratio := choose_ratio n r d hr hd
    rw [show r+(d-r)=d by omega]
    calc
      _ = (((d.choose r : ℝ)/(n.choose r : ℝ))*(n.choose d : ℝ))*
        x^r*x^(d-r)*(1-x)^((n-r)-(d-r)) := by ring
      _ = _ := by rw [hratio]; ring
  change (∑ d ∈ range (n+1), f d) = _
  rw [← Finset.sum_range_add_sum_Ico f (show r ≤ n+1 by omega), hlo, zero_add]
  rw [Finset.sum_Ico_eq_sum_range]
  have he : n+1-r = n-r+1 := by omega
  rw [he]
  calc
    _ = x^r * ∑ j ∈ range (n-r+1), bernsteinBasis (n-r) j x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [heq _ (by omega)]
      simp only [Nat.add_sub_cancel_left, bernsteinBasis]
      ring
    _ = x^r := by rw [bernsteinBasis_sum, mul_one]

lemma weighted_binomial_moment (m : ℕ → ℝ) (n j : ℕ) (hjn : j ≤ n) :
    ∑ p ∈ range (n+1), ((p.choose j : ℝ)/(n.choose j : ℝ))*weight m n p = m j := by
  have hp : (∑ p ∈ range (n+1), ((p.choose j : ℝ)/(n.choose j : ℝ)) •
      bernsteinPolynomial ℝ n p) = Polynomial.X^j := by
    apply Polynomial.funext
    intro x
    simpa [Polynomial.eval_finsetSum, Polynomial.eval_smul, bernsteinPolynomial,
      bernsteinBasis] using bernstein_monomial n j hjn x
  apply_fun momentFunctional m at hp
  simpa [weight] using hp

lemma falling_tendsto (j : ℕ) :
    Tendsto (fun n => falling n j) atTop (𝓝 (coordinate^j)) := by
  have hf (r : ℕ) : Tendsto (fun n : ℕ =>
      ((1-(r : ℝ)/n)⁻¹) • (coordinate - ((r : ℝ)/n) • (1 : C(I,ℝ)))) atTop
      (𝓝 coordinate) := by
    have h : Tendsto (fun n : ℕ => (r : ℝ)/n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h₁ := (tendsto_const_nhds.sub h).inv₀ (by norm_num : (1 : ℝ)-0 ≠ 0)
    simpa using h₁.smul (tendsto_const_nhds.sub (h.smul_const (1 : C(I,ℝ))))
  simpa [falling] using tendsto_finsetProd (range j) (fun _ _ => hf _)

lemma falling_grid (n p j : ℕ) (hn : 0 < n) (hjn : j ≤ n) (hp : p ≤ n) :
    falling n j ⟨(p : ℝ)/n, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        (div_le_one (by positivity)).mpr (by exact_mod_cast hp)⟩ =
      (p.choose j : ℝ)/(n.choose j : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [falling, ContinuousMap.prod_apply, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, coordinate, ContinuousMap.coe_mk, ContinuousMap.one_apply,
    smul_eq_mul, mul_one]
  calc
    _ = ∏ r ∈ range j, ((p : ℝ)-r)/((n : ℝ)-r) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hnr : (n : ℝ)-r ≠ 0 := by
        have : r < n := lt_of_lt_of_le (mem_range.mp hr) hjn
        exact sub_ne_zero.mpr (by exact_mod_cast this.ne')
      field_simp
    _ = (∏ r ∈ range j, ((p : ℝ)-r))/(∏ r ∈ range j, ((n : ℝ)-r)) := by
      rw [Finset.prod_div_distrib]
    _ = (p.descFactorial j : ℝ)/(n.descFactorial j : ℝ) := by
      rw [← descPochhammer_eval_eq_prod_range,
        ← descPochhammer_eval_eq_prod_range,
        descPochhammer_eval_eq_descFactorial,
        descPochhammer_eval_eq_descFactorial]
    _ = _ := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      exact mul_div_mul_left _ _ (by positivity : (j.factorial : ℝ) ≠ 0)

lemma gridMeasure_mass {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n : ℕ) :
    gridMeasure m n Set.univ = ENNReal.ofReal (m 0) := by
  simp only [gridMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun p : Fin (n+1) => weight m n p) (fun p _ => weight_nonneg hm n p)]
  congr 1
  simpa [Finset.sum_range] using weight_sum m n

lemma gridFiniteMeasure_mass {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n : ℕ) :
    (gridFiniteMeasure m n).mass = (m 0).toNNReal := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change gridMeasure m n _ = _
  rw [gridMeasure_mass hm]
  rfl

lemma integral_grid {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (n : ℕ)
    (f : C(I,ℝ)) :
    ∫ x, f x ∂gridMeasure m n = ∑ p : Fin (n+1), weight m n p * f (bernstein.z p) := by
  rw [gridMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p hp
    simp [ENNReal.toReal_ofReal (weight_nonneg hm n p)]
  · intro p hp
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

lemma integral_falling {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j)
    (n j : ℕ) (hn : 0 < n) (hjn : j ≤ n) :
    ∫ x, falling n j x ∂gridMeasure m n = m j := by
  rw [integral_grid hm]
  have he (p : Fin (n+1)) : falling n j (bernstein.z p) =
      (p.val.choose j : ℝ)/(n.choose j : ℝ) := falling_grid n p j hn hjn p.is_le
  simp_rw [he, mul_comm (weight m n _) ]
  simpa [Finset.sum_range] using weighted_binomial_moment m n j hjn

lemma grid_moments_tendsto {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) (j : ℕ) :
    Tendsto (fun n => ∫ x : I, (x : ℝ)^j ∂gridMeasure m n) atTop (𝓝 (m j)) := by
  have herr : Tendsto (fun n => ‖coordinate^j-falling n j‖*(m 0)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := coordinate^j)).sub (falling_tendsto j)).norm.mul_const (m 0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' _ _ herr
  · filter_upwards [] with n using norm_nonneg _
  · filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop j] with n hn hjn
    rw [← integral_falling hm n j hn hjn]
    rw [← integral_sub (by exact (coordinate^j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((falling n j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have h := norm_integral_le_of_norm_le_const (μ := gridMeasure m n)
      (C := ‖coordinate^j-falling n j‖)
      (Filter.Eventually.of_forall (fun x => (coordinate^j-falling n j).norm_coe_le_norm x))
    simpa [coordinate, Measure.real, gridMeasure_mass hm, ENNReal.toReal_ofReal (show 0 ≤ m 0 from hm 0 0)] using h

theorem hausdorff {m : ℕ → ℝ} (hm : ∀ r j, 0 ≤ difference m r j) :
    ∃ μ : FiniteMeasure I, (μ.mass : ℝ) = m 0 ∧
      ∀ j : ℕ, (∫ x : I, (x : ℝ)^j ∂(μ : Measure I)) = m j := by
  have h0 : 0 ≤ m 0 := hm 0 0
  obtain ⟨μ, hμ, hlim⟩ :=
    (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace I (m 0).toNNReal).exists_mapClusterPt
      (Filter.le_principal_iff.mpr
        (show ∀ᶠ ν in Filter.map (gridFiniteMeasure m) atTop, ν.mass = (m 0).toNNReal from
          Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun n => gridFiniteMeasure_mass hm n))))
  refine ⟨μ, by simpa [Real.toNNReal_of_nonneg h0] using congrArg NNReal.toReal hμ, fun j => ?_⟩
  have hw := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (show Tendsto (id : FiniteMeasure I → FiniteMeasure I) (𝓝 μ) (𝓝 μ) from tendsto_id) (ContinuousMap.equivBoundedOfCompact I ℝ (coordinate^j))
  have hc := hlim.tendsto_comp hw
  have hd := grid_moments_tendsto hm j
  apply eq_of_nhds_neBot
  exact (show NeBot (𝓝 (∫ x : I, (x : ℝ)^j ∂(μ : Measure I)) ⊓ Filter.map (fun n => ∫ x : I, (x : ℝ)^j ∂gridMeasure m n) atTop) from hc).mono (inf_le_inf_left _ hd)

lemma CM.deriv_differentiableOn {g : ℝ → ℝ} (hg : CM g) (r : ℕ) :
    DifferentiableOn ℝ (iteratedDeriv r g) (Set.Ioi 0) := by
  have hd := hg.1.differentiableOn_iteratedDerivWithin (m := r)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl r) isOpen_Ioi.uniqueDiffOn
  exact hd.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)

lemma CM.signed_antitone {g : ℝ → ℝ} (hg : CM g) (r : ℕ) :
    AntitoneOn (fun x => (-1 : ℝ)^r * iteratedDeriv r g x) (Set.Ioi 0) := by
  have hd := (hg.deriv_differentiableOn r).const_mul ((-1 : ℝ)^r)
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _) hd.continuousOn
  · simpa only [interior_Ioi] using hd
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    have hdx := (hg.deriv_differentiableOn r x hx').differentiableAt (Ioi_mem_nhds hx')
    rw [deriv_const_mul_field, ← iteratedDeriv_succ]
    have hs := hg.2 (r+1) x hx'
    simp only [pow_succ, mul_neg_one] at hs
    linarith

lemma CM.shift {g : ℝ → ℝ} (hg : CM g) {d : ℝ} (hd : 0 ≤ d) :
    CM (fun x => g (x+d)) := by
  constructor
  · exact hg.1.comp ((contDiff_id.add contDiff_const).contDiffOn) (fun x hx => add_pos_of_pos_of_nonneg hx hd)
  · intro r x hx
    rw [iteratedDeriv_comp_add_const]
    exact hg.2 r _ (by linarith)

lemma CM.sub_shift {g : ℝ → ℝ} (hg : CM g) {d : ℝ} (hd : 0 ≤ d) :
    CM (fun x => g x-g (x+d)) := by
  refine ⟨hg.1.sub (hg.shift hd).1, ?_⟩
  intro r x hx
  have hgx : ContDiffAt ℝ r g x := (hg.1.contDiffAt (Ioi_mem_nhds hx)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  have hgdx : ContDiffAt ℝ r (fun x => g (x+d)) x :=
    ((hg.shift hd).1.contDiffAt (Ioi_mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl r)
  rw [iteratedDeriv_fun_sub hgx hgdx, iteratedDeriv_comp_add_const, mul_sub]
  exact sub_nonneg.mpr (hg.signed_antitone r hx (add_pos_of_pos_of_nonneg hx hd) (le_add_of_nonneg_right hd))

lemma difference_shift (m : ℕ → ℝ) (r j : ℕ) :
    difference (fun k => m k-m (k+1)) r j = difference m (r+1) j := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih => simp only [difference, ih]

lemma CM.sample_difference {g : ℝ → ℝ} (hg : CM g) {ε d : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (r j : ℕ) :
    0 ≤ difference (fun j : ℕ => g (ε+j*d)) r j := by
  induction r generalizing g j with
  | zero => simpa [difference] using hg.2 0 (ε+j*d) (by positivity)
  | succ r ih =>
    have h := ih (hg.sub_shift hd) j
    have he : (fun j : ℕ => g (ε+j*d)-g (ε+j*d+d)) =
        (fun j : ℕ => g (ε+j*d)-g (ε+((j+1 : ℕ) : ℝ)*d)) := by
      funext j
      congr 2; push_cast <;> ring
    rw [he, difference_shift] at h
    exact h

lemma continuous_powerTest : Continuous powerTest := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_subtype_val.comp continuous_snd).rpow
    (continuous_subtype_val.comp continuous_fst) (fun p => Or.inr p.1.property)

lemma mass_map_unitPower (μ : FiniteMeasure I) (n : ℕ) :
    (μ.map (unitPower n)).mass = μ.mass := by
  exact μ.map_apply (unitPower n).continuous.measurable MeasurableSet.univ

lemma integral_power_map (μ : FiniteMeasure I) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∫ v : I, (v : ℝ) ^ ((j : ℝ)/n) ∂(μ.map (unitPower n) : Measure I) =
      ∫ v : I, (v : ℝ)^j ∂(μ : Measure I) := by
  rw [FiniteMeasure.toMeasure_map]
  have hmap := integral_map (μ := (μ : Measure I)) (f := fun v : I => (v : ℝ)^((j : ℝ)/n))
    (unitPower n).continuous.measurable.aemeasurable
    (((Real.continuous_rpow_const (by positivity : 0 ≤ (j : ℝ)/n)).comp continuous_subtype_val).aestronglyMeasurable)
  rw [hmap]
  congr 1
  funext v
  change ((v : ℝ)^n) ^ ((j : ℝ)/n) = (v : ℝ)^j
  rw [← Real.rpow_natCast, ← Real.rpow_mul v.property.1]
  rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0), Real.rpow_natCast]

lemma gridTime_pos (t : ℝ) (n : ℕ) : 0 < gridTime t n := by
  unfold gridTime
  positivity

lemma gridTime_tendsto {t : ℝ} (ht : 0 ≤ t) : Tendsto (gridTime t) atTop (𝓝 t) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hf := (tendsto_nat_floor_mul_div_atTop ht).comp hn
  have hi := tendsto_inv_atTop_zero.comp hn
  convert hf.add hi using 1
  · funext n
    simp [gridTime, add_div, one_div]
  · simp

theorem mixture_of_differences {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ici 0))
    (hD : ∀ d : ℝ, 0 < d → ∀ r j : ℕ,
      0 ≤ difference (fun j : ℕ => F (j*d)) r j) :
    ∃ ρ : FiniteMeasure I, (ρ.mass : ℝ) = F 0 ∧
      ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t := by
  have h0 : 0 ≤ F 0 := by simpa [difference] using hD 1 zero_lt_one 0 0
  have hex (n : ℕ) := hausdorff (hD (1/((n : ℝ)+1)) (by positivity))
  choose η hηmass hηmoment using hex
  let ρseq (n : ℕ) : FiniteMeasure I := (η n).map (unitPower (n+1))
  have hm (n : ℕ) : ((ρseq n).mass : ℝ) = F 0 := by
    simpa [ρseq, mass_map_unitPower] using hηmass n
  obtain ⟨ρ, hρ, hlim⟩ :=
    (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace I (F 0).toNNReal).exists_mapClusterPt
      (Filter.le_principal_iff.mpr
        (show ∀ᶠ ν in Filter.map ρseq atTop, ν.mass = (F 0).toNNReal from
          Filter.eventually_map.mpr (Filter.Eventually.of_forall (fun n => by
            apply NNReal.eq
            simpa [Real.toNNReal_of_nonneg h0] using hm n))))
  refine ⟨ρ, by simpa [Real.toNNReal_of_nonneg h0] using congrArg NNReal.toReal hρ, ?_⟩
  intro t ht
  let tj (n : ℕ) : ℕ := ⌊t*((n : ℝ)+1)⌋₊+1
  let tn (n : ℕ) : Positive := ⟨gridTime t n, gridTime_pos t n⟩
  have he (n : ℕ) : ∫ v : I, (v : ℝ)^(gridTime t n) ∂(ρseq n : Measure I) = F (gridTime t n) := by
    have h := integral_power_map (η n) (Nat.succ_pos n) (tj n)
    have hh := hηmoment n (tj n)
    simp only [div_eq_mul_inv] at h hh
    simpa [ρseq, gridTime, tj, Nat.cast_add, Nat.cast_one, div_eq_mul_inv] using h.trans hh
  have htest : Tendsto (fun n => powerTest (tn n)) atTop (𝓝 (powerTest ⟨t, ht⟩)) :=
    continuous_powerTest.tendsto _ |>.comp (tendsto_subtype_rng.mpr (gridTime_tendsto ht.le))
  have herr : Tendsto (fun n => ‖powerTest ⟨t, ht⟩ - powerTest (tn n)‖ * F 0) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := powerTest ⟨t, ht⟩)).sub htest).norm.mul_const (F 0)
  have hdiff : Tendsto (fun n =>
      (∫ v : I, (v : ℝ)^t ∂(ρseq n : Measure I)) - F (gridTime t n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ herr
    intro n
    rw [← he n]
    change ‖(∫ v, powerTest ⟨t, ht⟩ v ∂(ρseq n : Measure I)) -
      (∫ v, powerTest (tn n) v ∂(ρseq n : Measure I))‖ ≤ _
    rw [← integral_sub
      ((powerTest ⟨t, ht⟩).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((powerTest (tn n)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hb := norm_integral_le_of_norm_le_const (μ := (ρseq n : Measure I))
      (C := ‖powerTest ⟨t, ht⟩ - powerTest (tn n)‖)
      (Filter.Eventually.of_forall (fun v => (powerTest ⟨t, ht⟩ - powerTest (tn n)).norm_coe_le_norm v))
    simpa only [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal, hm, ContinuousMap.sub_apply] using hb
  have hFt : Tendsto (fun n => F (gridTime t n)) atTop (𝓝 (F t)) :=
    (hF.continuousAt (Ici_mem_nhds ht)).tendsto.comp (gridTime_tendsto ht.le)
  have hd : Tendsto (fun n => ∫ v : I, (v : ℝ)^t ∂(ρseq n : Measure I)) atTop (𝓝 (F t)) := by
    convert hdiff.add hFt using 1 <;> first | (with_reducible_and_instances rfl) | (simp)
  have hw := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (show Tendsto (id : FiniteMeasure I → FiniteMeasure I) (𝓝 ρ) (𝓝 ρ) from tendsto_id)
    (ContinuousMap.equivBoundedOfCompact I ℝ (powerTest ⟨t, ht⟩))
  have hc := hlim.tendsto_comp hw
  apply eq_of_nhds_neBot
  exact (show NeBot (𝓝 (∫ v : I, (v : ℝ)^t ∂(ρ : Measure I)) ⊓
    Filter.map (fun n => ∫ v : I, (v : ℝ)^t ∂(ρseq n : Measure I)) atTop) from hc).mono
      (inf_le_inf_left _ hd)

theorem CM.shifted_mixture {g : ℝ → ℝ} (hg : CM g) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : FiniteMeasure I, (ρ.mass : ℝ) = g ε ∧
      ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = g (ε+t) := by
  have hc : ContinuousOn (fun t => g (ε+t)) (Set.Ici 0) :=
    hg.1.continuousOn.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => add_pos_of_pos_of_nonneg hε ht)
  have hd (d : ℝ) (hd : 0 < d) (r j : ℕ) :
      0 ≤ difference (fun j : ℕ => g (ε+j*d)) r j :=
    hg.sample_difference hε hd.le r j
  simpa using mixture_of_differences hc hd

end TriangularUniversal.PositiveMixture

open MeasureTheory
namespace TriangularUniversal
open PositiveMixture

lemma powerPotential_continuous {t : ℝ} (ht : 0 ≤ t) :
    Continuous (fun v : I => powerPotential v t) :=
  (Real.continuous_rpow_const ht).comp continuous_subtype_val

lemma measurable_diskEnergy_power (C : Set Plane) (R : ℝ) :
    Measurable (fun v : I => diskEnergy (powerPotential v) C R) := by
  unfold diskEnergy
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x hx
  apply Finset.measurable_sum
  intro y hy
  exact ENNReal.continuous_ofReal.measurable.comp (powerPotential_continuous (sq_nonneg _)).measurable

lemma lintegral_power_eq (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ v : I, ENNReal.ofReal (powerPotential v t) ∂(ρ : Measure I) = ENNReal.ofReal (F t) := by
  rw [← hF t ht]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((powerTest ⟨t, ht⟩).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall (fun v => Real.rpow_nonneg v.property.1 _))).symm

lemma lintegral_diskEnergy_power (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t)
    (C : Set Plane) (R : ℝ) :
    ∫⁻ v : I, diskEnergy (powerPotential v) C R ∂(ρ : Measure I) = diskEnergy F C R := by
  unfold diskEnergy
  rw [lintegral_const_mul]
  · congr 1
    rw [lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro y hy
        exact lintegral_power_eq ρ F hF (sq_pos_of_pos (norm_pos_iff.mpr
          (sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)))
      · intro y hy
        exact (ENNReal.continuous_ofReal.measurable.comp
          (powerPotential_continuous (sq_nonneg _)).measurable)
    · intro x hx
      apply Finset.measurable_sum
      intro y hy
      exact ENNReal.continuous_ofReal.measurable.comp
        (powerPotential_continuous (sq_nonneg _)).measurable
  · apply Finset.measurable_sum
    intro x hx
    apply Finset.measurable_sum
    intro y hy
    exact ENNReal.continuous_ofReal.measurable.comp
      (powerPotential_continuous (sq_nonneg _)).measurable

lemma mixture_energy_lower (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t)
    (C : Set Plane) :
    ∫⁻ v : I, energy (powerPotential v) C ∂(ρ : Measure I) ≤ energy F C := by
  have h := lintegral_liminf_le (μ := (ρ : Measure I)) (u := (atTop : Filter ℝ))
    (fun R : ℝ => measurable_diskEnergy_power C R)
  simpa only [energy, lintegral_diskEnergy_power ρ F hF C] using h

lemma lintegral_latticeEnergy_power (ρ : FiniteMeasure I) (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∫ v : I, (v : ℝ)^t ∂(ρ : Measure I) = F t) :
    ∫⁻ v : I, latticeEnergy (powerPotential v) ∂(ρ : Measure I) = latticeEnergy F := by
  unfold latticeEnergy
  rw [lintegral_tsum]
  · apply tsum_congr
    intro a
    exact lintegral_power_eq ρ F hF (sq_pos_of_pos (norm_pos_iff.mpr a.property.2))
  · intro a
    exact (ENNReal.continuous_ofReal.measurable.comp
      (powerPotential_continuous (sq_nonneg _)).measurable).aemeasurable

theorem shifted_mixture_energy (g : ℝ → ℝ) (hg : AdmissiblePotential g)
    {ε : ℝ} (hε : 0 < ε) (C : Set Plane) :
    ∃ ρ : FiniteMeasure I, (ρ.mass : ℝ) = g ε ∧
      (∫⁻ v : I, latticeEnergy (powerPotential v) ∂(ρ : Measure I)) =
        latticeEnergy (fun t => g (ε+t)) ∧
      (∫⁻ v : I, energy (powerPotential v) C ∂(ρ : Measure I)) ≤
        energy (fun t => g (ε+t)) C := by
  obtain ⟨ρ, hm, hρ⟩ := CM.shifted_mixture ⟨hg.1, hg.2.2⟩ hε
  exact ⟨ρ, hm, lintegral_latticeEnergy_power ρ _ hρ, mixture_energy_lower ρ _ hρ C⟩
end TriangularUniversal

namespace TriangularUniversal
open PositiveMixture

lemma potential_antitone {g : ℝ → ℝ} (hg : AdmissiblePotential g) :
    AntitoneOn g (Set.Ioi 0) := by
  simpa using (CM.signed_antitone ⟨hg.1, hg.2.2⟩ 0)

lemma diskEnergy_mono {f g : ℝ → ℝ} (hfg : ∀ t, 0 < t → f t ≤ g t)
    (C : Set Plane) (R : ℝ) : diskEnergy f C R ≤ diskEnergy g C R := by
  unfold diskEnergy
  gcongr with x hx y hy
  exact hfg _ (sq_pos_of_pos (norm_pos_iff.mpr
    (sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm)))

lemma energy_mono {f g : ℝ → ℝ} (hfg : ∀ t, 0 < t → f t ≤ g t) (C : Set Plane) :
    energy f C ≤ energy g C :=
  liminf_le_liminf (Filter.Eventually.of_forall (diskEnergy_mono hfg C))

lemma latticeEnergy_mono {f g : ℝ → ℝ} (hfg : ∀ t, 0 < t → f t ≤ g t) :
    latticeEnergy f ≤ latticeEnergy g := by
  apply ENNReal.tsum_le_tsum
  intro a
  exact ENNReal.ofReal_le_ofReal (hfg _ (sq_pos_of_pos (norm_pos_iff.mpr a.property.2)))

lemma shifted_energy_le {g : ℝ → ℝ} (hg : AdmissiblePotential g)
    {ε : ℝ} (hε : 0 ≤ ε) (C : Set Plane) :
    energy (fun t => g (ε+t)) C ≤ energy g C := by
  apply energy_mono
  intro t ht
  exact potential_antitone hg ht (add_pos_of_nonneg_of_pos hε ht) (le_add_of_nonneg_left hε)

lemma latticeEnergy_shift_iSup {g : ℝ → ℝ} (hg : AdmissiblePotential g) :
    latticeEnergy g = ⨆ n : ℕ, latticeEnergy (fun t => g (1/((n:ℝ)+1)+t)) := by
  apply le_antisymm
  · apply ENNReal.summable.tsum_le_of_sum_le
    intro F
    have hc (a : NonzeroSite) :
        Tendsto (fun n : ℕ => ENNReal.ofReal (g (1/((n:ℝ)+1)+‖a.val‖^2))) atTop
          (𝓝 (ENNReal.ofReal (g (‖a.val‖^2)))) := by
      have ht : 0 < ‖a.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr a.property.2)
      have hg' := hg.1.continuousOn.continuousAt (IsOpen.mem_nhds isOpen_Ioi ht)
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      apply hg'.tendsto.comp
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add_const (‖a.val‖^2)
    have hf := tendsto_finsetSum F (fun a _ => hc a)
    apply le_of_tendsto hf
    apply Filter.Eventually.of_forall
    intro n
    exact (ENNReal.sum_le_tsum F).trans (le_iSup (fun n : ℕ =>
      latticeEnergy (fun t => g (1/((n:ℝ)+1)+t))) n)
  · apply iSup_le
    intro n
    apply latticeEnergy_mono
    intro t ht
    have hε : 0 < 1/((n:ℝ)+1) := by positivity
    exact potential_antitone hg ht (add_pos hε ht) (le_add_of_nonneg_left hε.le)

end TriangularUniversal
end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Lattice_LatticeGeometry
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace AtomicTriangular
lemma triangular_scale_eq : (Real.sqrt b)⁻¹=Real.sqrt (2/Real.sqrt 3) := by
  rw [←Real.sqrt_inv]
  congr 1
  simp [b,inv_div]
lemma triangularPoint_eq_support (v : ℤ × ℤ) : triangularPoint v=TriangularUniversal.triangularPoint v := by
  unfold triangularPoint TriangularUniversal.triangularPoint
  rw [triangular_scale_eq]
  congr 2
  unfold b
  ring_nf
lemma b_pos : 0 < b := by unfold b; positivity
lemma triangularPoint_norm_sq (j k : ℤ) :
    b*‖triangularPoint (j,k)‖^2=(j:ℝ)^2+(j:ℝ)*k+(k:ℝ)^2 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_norm_sq j k
lemma A_eq_support : A=TriangularUniversal.triangularLattice := by
  unfold A TriangularUniversal.triangularLattice
  congr 1
  exact funext triangularPoint_eq_support
lemma eisenstein_mod36_finite : ∀ j k : Fin 36,
    ((j.val:ℤ)^2+(j.val:ℤ)*k.val+(k.val:ℤ)^2)%36∈Construction.residues := by decide +kernel
lemma eisenstein_mod36 (j k : ℤ) :
    (j^2+j*k+k^2)%36∈Construction.residues := by
  let j' : Fin 36 := ⟨(j%36).toNat,by have := Int.emod_nonneg j (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos j (by norm_num : (0:ℤ)<36); omega⟩
  let k' : Fin 36 := ⟨(k%36).toNat,by have := Int.emod_nonneg k (by norm_num : (36:ℤ)≠0); have := Int.emod_lt_of_pos k (by norm_num : (0:ℤ)<36); omega⟩
  have hj : (j'.val:ℤ)=j%36 := Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num))
  have hk : (k'.val:ℤ)=k%36 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
  have hh := eisenstein_mod36_finite j' k'
  rw [hj,hk] at hh
  simpa [Int.add_emod,Int.mul_emod,pow_two,Int.emod_emod] using hh
lemma A_radial_node {x : Plane} (hx : x∈A) (hx0 : x≠0) :
    ∃ n : Construction.Node,Construction.radial x=n.val := by
  obtain ⟨⟨j,k⟩,rfl⟩ := hx
  let n : ℤ := j^2+j*k+k^2
  have he : Construction.radial (triangularPoint (j,k))=(n:ℝ) := by
    change b*‖triangularPoint (j,k)‖^2=_
    rw [triangularPoint_norm_sq]
    dsimp [n]
    push_cast
    rfl
  have hn : 0 < n := by
    have hp : 0 < Construction.radial (triangularPoint (j,k)) :=
      mul_pos b_pos (sq_pos_of_pos (norm_pos_iff.mpr hx0))
    rw [he] at hp
    exact_mod_cast hp
  exact ⟨⟨n,hn,eisenstein_mod36 j k⟩,he⟩
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Lattice
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace TriangularUniversal
lemma latticeEnergy_nonzero_index (g : ℝ → ℝ) :
    latticeEnergy g=∑' v : {v : ℤ × ℤ // v≠0}, ENNReal.ofReal (g (‖triangularPoint v.val‖^2)) := by
  exact (nonzeroLatticeEquiv.tsum_eq (fun x : NonzeroSite => ENNReal.ofReal (g (‖x.val‖^2)))).symm
end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Schwartz
attribute [-instance] _root_.OAI.TriangularUniversal.instDiscreteTopologySubtypePlaneMemSubmoduleIntTriangularModule _root_.OAI.TriangularUniversal.instIsZLatticeRealPlaneTriangularModule _root_.OAI.TriangularUniversal.nonzeroSite_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory FourierTransform
namespace AtomicTriangular

lemma complexSchwartz_apply (f : 𝓢(Plane,ℝ)) (x : Plane) : complexSchwartz f x=(f x:ℂ) := by
  simp only [complexSchwartz,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply]
lemma schwartzLP_apply (f : 𝓢(Plane,ℝ)) (x : Plane) : schwartzLP f x=(f x:ℂ) :=
  complexSchwartz_apply f x
lemma schwartzLP_fourier (f : 𝓢(Plane,ℝ)) (w : Plane) :
    𝓕 (schwartzLP f : Plane → ℂ) w=realFourier f w := by
  congr 1
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal
open Complex MeasureTheory
namespace AtomicTriangular

lemma schwartzLP_integral {α : ℝ} (p : GaussianPair α) :
    (∫ z, schwartzLP p.first z)=(p.second 0:ℂ) := by
  rw [←TriangularUniversal.fourier_zero_eq_integral,schwartzLP_fourier,p.fourier_first]

lemma triangularPoint_zero : triangularPoint (0 : ℤ × ℤ)=0 := by
  rw [triangularPoint_eq_support]
  exact TriangularUniversal.triangularPoint_zero
lemma triangularPoint_ne_zero {v : ℤ × ℤ} (hv : v≠0) : triangularPoint v≠0 := by
  rw [triangularPoint_eq_support]
  exact mt (TriangularUniversal.triangularPoint_eq_zero_iff v).mp hv
lemma GaussianPair.lattice_contact {α : ℝ} (p : GaussianPair α) (v : ℤ × ℤ) (hv : v≠0) :
    p.first (triangularPoint v)=gaussPot α (‖triangularPoint v‖^2) := by
  obtain ⟨n,hn⟩ := A_radial_node (show triangularPoint v∈A from ⟨v,rfl⟩) (triangularPoint_ne_zero hv)
  exact p.contact _ n hn
lemma GaussianPair.lattice_zeros {α : ℝ} (p : GaussianPair α) (v : ℤ × ℤ) (hv : v≠0) :
    p.second (triangularPoint v)=0 := by
  obtain ⟨n,hn⟩ := A_radial_node (show triangularPoint v∈A from ⟨v,rfl⟩) (triangularPoint_ne_zero hv)
  exact p.zeros _ n hn
lemma latticeEnergy_eq_support (g : ℝ → ℝ) : latticeEnergy g=TriangularUniversal.latticeEnergy g := by
  unfold latticeEnergy TriangularUniversal.latticeEnergy
  rw [A_eq_support]
lemma GaussianPair.sharp_value {α : ℝ} (p : GaussianPair α) (hp : GaussianLatticePoisson p) :
    latticeEnergy (gaussPot α)=ENNReal.ofReal (p.second 0-p.first 0) := by
  classical
  have hsum : (∑' v : ℤ × ℤ, p.first (triangularPoint v))=p.second 0 := by
    rw [hp.poisson,tsum_eq_single 0 (fun v hv => p.lattice_zeros v hv),triangularPoint_zero]
  have hadd : p.first 0+(∑' v : {v : ℤ × ℤ // v≠0},p.first (triangularPoint v.val))=p.second 0 := by
    have hh := hp.first_summable.sum_add_tsum_subtype_compl ({0}:Finset (ℤ × ℤ))
    simp only [Finset.sum_singleton,triangularPoint_zero,hsum] at hh
    let e : {x : ℤ × ℤ // x ∉ ({0} : Finset (ℤ × ℤ))} ≃ {v : ℤ × ℤ // v≠0} :=
      Equiv.subtypeEquivRight (fun v => by simp only [Finset.mem_singleton])
    have he : (∑' x : {x : ℤ × ℤ // x ∉ ({0} : Finset (ℤ × ℤ))},p.first (triangularPoint x.val))=
        ∑' v : {v : ℤ × ℤ // v≠0},p.first (triangularPoint v.val) :=
      e.tsum_eq (fun v => p.first (triangularPoint v.val))
    exact he ▸ hh
  have hs := hp.first_summable.subtype (fun v : ℤ × ℤ => v≠0)
  have he (v : {v : ℤ × ℤ // v≠0}) : p.first (triangularPoint v.val)=gaussPot α (‖triangularPoint v.val‖^2) :=
    p.lattice_contact v.val v.property
  have hs' : Summable (fun v : {v : ℤ × ℤ // v≠0} => gaussPot α (‖triangularPoint v.val‖^2)) := by
    exact hs.congr (fun v => he v)
  rw [latticeEnergy_eq_support,TriangularUniversal.latticeEnergy_nonzero_index]
  simp_rw [←triangularPoint_eq_support]
  rw [←ENNReal.ofReal_tsum_of_nonneg (f := fun v : {v : ℤ × ℤ // v≠0} => gaussPot α (‖triangularPoint v.val‖^2)) (fun v : {v : ℤ × ℤ // v≠0} => (Real.exp_pos (-Real.pi*α*‖triangularPoint v.val‖^2)).le) hs']
  congr 1
  simp_rw [he] at hadd
  linarith
lemma GaussianPair.energy_bound {α : ℝ} (p : GaussianPair α) (hp : GaussianLatticePoisson p)
    {C : Set Plane} (hD : DensityOne C) : latticeEnergy (gaussPot α)≤energy (gaussPot α) C := by
  rw [p.sharp_value hp]
  have he : (∫ z,schwartzLP p.first z).re-(schwartzLP p.first 0).re=p.second 0-p.first 0 := by
    rw [schwartzLP_integral,schwartzLP_apply]
    rfl
  rw [←he]
  apply TriangularUniversal.density_lp (schwartzLP p.first)
  · intro w
    rw [schwartzLP_fourier,p.fourier_first]
    rfl
  · intro w
    rw [schwartzLP_fourier,p.fourier_first]
    exact p.positive w
  · intro x _
    rw [schwartzLP_apply]
    exact p.minorant x
  · exact hD
lemma gaussian_energy_bound {C : Set Plane} (hD : DensityOne C) (α : ℝ) (hα : 0<α) :
    latticeEnergy (gaussPot α)≤energy (gaussPot α) C :=
  (gaussianPair α hα).energy_bound (gaussianPair_poisson_eu α hα) hD
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Potentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open Filter MeasureTheory
namespace TriangularUniversal
open PositiveMixture
/-- The shift/Fatou/Tonelli assembly applies to the exact extended ordered-pair
energy. It does not presume finite lattice energy or spacing of a competitor. -/
lemma universal_from_power_bounds (C : Set Plane)
    (hpower : ∀ v : I, latticeEnergy (powerPotential v) ≤ energy (powerPotential v) C)
    {g : ℝ → ℝ} (hg : AdmissiblePotential g) : latticeEnergy g ≤ energy g C := by
  rw [latticeEnergy_shift_iSup hg]
  apply iSup_le
  intro n
  have hε : 0<(1:ℝ)/(n+1) := by positivity
  obtain ⟨ρ,_,he,hl⟩ := shifted_mixture_energy g hg hε C
  rw [← he]
  apply (lintegral_mono (fun v => hpower v)).trans
  exact hl.trans (shifted_energy_le hg hε.le C)
end TriangularUniversal
end

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter
namespace TriangularUniversal
lemma diskEnergy_one {C : Set Plane} {R : ℝ} (hN : 0<diskCount C R) :
    diskEnergy (fun _ => 1) C R=((diskCount C R-1:ℕ):ℝ≥0∞) := by
  classical
  have hs : (∑ x ∈ diskPoints C R, ∑ _y ∈ (diskPoints C R).erase x, (1:ℝ≥0∞))=
      (diskCount C R:ℝ≥0∞)*((diskCount C R-1:ℕ):ℝ≥0∞) := by
    calc
      _=∑ _x ∈ diskPoints C R, ((diskCount C R-1:ℕ):ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.sum_const,Finset.card_erase_of_mem hx,nsmul_eq_mul,mul_one,diskCount]
      _=_ := by simp only [Finset.sum_const,nsmul_eq_mul,diskCount]
  unfold diskEnergy
  simp only [ENNReal.ofReal_one]
  rw [hs,← mul_assoc,ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp),one_mul]
lemma count_sub_one_tendsto {C : Set Plane} (hD : DensityOne C) :
    Tendsto (fun R : ℝ => ((diskCount C R-1:ℕ):ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  have hp := hD.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  filter_upwards [hp,eventually_ge_atTop (max (1:ℝ) (K+2)),density_count_eventually_pos hD] with R h hR hn
  have hR1 : 1≤R := le_trans (le_max_left _ _) hR
  have hRK : K+2≤R := le_trans (le_max_right _ _) hR
  have hrp : 0<R := by linarith
  have hh := (lt_div_iff₀ (mul_pos Real.pi_pos (sq_pos_of_pos hrp))).mp h
  have hn' : (1:ℕ)≤diskCount C R := hn
  rw [Nat.cast_sub hn',Nat.cast_one]
  have hpi := Real.pi_gt_three
  have hp2 := mul_le_mul_of_nonneg_right hpi.le (sq_nonneg R)
  nlinarith [sq_nonneg (R-1)]
lemma energy_one {C : Set Plane} (hD : DensityOne C) : energy (fun _ => 1) C=∞ := by
  have ht := ENNReal.tendsto_ofReal_atTop.comp (count_sub_one_tendsto hD)
  have he : (fun R : ℝ => diskEnergy (fun _ => 1) C R)=ᶠ[atTop]
      (fun R : ℝ => ENNReal.ofReal ((diskCount C R-1:ℕ):ℝ)) := by
    filter_upwards [density_count_eventually_pos hD] with R hR
    rw [diskEnergy_one hR,ENNReal.ofReal_natCast]
  exact (ht.congr' he.symm).liminf_eq
end TriangularUniversal
end

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
namespace TriangularUniversal
open PositiveMixture
lemma power_bounds_from_gaussians {C : Set Plane} (hD : DensityOne C)
    (hgauss : ∀ α : ℝ, 0<α → latticeEnergy (gaussPot α)≤energy (gaussPot α) C)
    (v : I) : latticeEnergy (powerPotential v)≤energy (powerPotential v) C := by
  by_cases h0 : (v:ℝ)=0
  · have hl : latticeEnergy (powerPotential v)=0 := by
      unfold latticeEnergy
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      have ht : 0<‖x.val‖^2 := sq_pos_of_pos (norm_pos_iff.mpr x.property.2)
      simp only [powerPotential,h0,Real.zero_rpow ht.ne',ENNReal.ofReal_zero]
    rw [hl]
    exact zero_le
  by_cases h1 : (v:ℝ)=1
  · have he : powerPotential v=(fun _ => (1:ℝ)) := by
      funext t
      simp only [powerPotential,h1,Real.one_rpow]
    rw [he,energy_one hD]
    exact le_top
  have hv : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm h0)
  have hv1 : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 h1
  let α : ℝ := -Real.log (v:ℝ)/Real.pi
  have hα : 0<α := div_pos (neg_pos.mpr (Real.log_neg hv hv1)) Real.pi_pos
  have he : powerPotential v=gaussPot α := by
    funext t
    rw [powerPotential,Real.rpow_def_of_pos hv]
    unfold gaussPot
    congr 1
    dsimp [α]
    field_simp
  rw [he]
  exact hgauss α hα
lemma universal_from_gaussian_bounds {C : Set Plane} (hD : DensityOne C)
    (hgauss : ∀ α : ℝ, 0<α → latticeEnergy (gaussPot α)≤energy (gaussPot α) C)
    {g : ℝ → ℝ} (hg : AdmissiblePotential g) :
    latticeEnergy g≤energy g C ∧ latticeEnergy g=energy g triangularLattice :=
  ⟨universal_from_power_bounds C (power_bounds_from_gaussians hD hgauss) hg,lattice_energy_eq g⟩
end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Universal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace AtomicTriangular
/-- The triangular lattice minimizes every nonnegative completely monotone energy. -/
theorem universal_energy_minimum_oai (g : ℝ → ℝ) (C : Set Plane)
    (hg : AdmissiblePotential g) (_hC : LocallyFinite C) (hd : DensityOne C) :
    latticeEnergy g ≤ energy g C ∧ latticeEnergy g = energy g A := by
  have hb (α : ℝ) (hα : 0<α) :
      TriangularUniversal.latticeEnergy (TriangularUniversal.gaussPot α)≤
        TriangularUniversal.energy (TriangularUniversal.gaussPot α) C := by
    rw [←latticeEnergy_eq_support]
    exact gaussian_energy_bound hd α hα
  have hu := TriangularUniversal.universal_from_gaussian_bounds hd hb hg
  constructor
  · rw [latticeEnergy_eq_support]
    exact hu.1
  · rw [latticeEnergy_eq_support,A_eq_support]
    exact hu.2
end AtomicTriangular
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.universal_energy_minimum_oai := @OAI.AtomicTriangular.universal_energy_minimum_oai
