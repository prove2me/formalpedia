-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.Herglotz.pick_divided_difference_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:19:32.825618+00:00
-- url     : https://prove2.me/submissions/cff92ce5-e31c-4145-ae5e-f2acea63c54a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean:L860-L895
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.Herglotz.pick_divided_difference_of_continuous. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_compactDen_ne_zero
import Theorems.Thm_OAI_EntropyPhotonNumber_Herglotz_tendsto_integral_varying

-- ---- from OAI.Analysis.Herglotz ----
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem integral_densityMeasure (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) (g : X → ℝ) :
    (∫ x, g x ∂(densityMeasure μ f : Measure X)) = ∫ x, f x * g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (f x)) from
      ENNReal.measurable_ofReal.comp f.continuous.measurable)
    (by simp : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) < ∞)]
  simp only [ENNReal.toReal_ofReal (hf _), smul_eq_mul]

end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

end WeakIntegral

attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle
theorem integral_angle (F : ℝ → ℝ) :
    (∫ θ : Angle, F θ) = ∫ θ in (0 : ℝ)..2 * Real.pi, F θ := by
  rw [integral_subtype measurableSet_Icc F, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by positivity)]

theorem radialDensity_nonneg {v : ℂ → ℝ} {R : ℝ}
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) (θ : Angle) :
    0 ≤ RadialDensity v R hv hR θ := by
  apply mul_nonneg (by positivity)
  apply hn
  simp only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hR.1]
  exact hR.2

theorem integral_radialMeasure {v : ℂ → ℝ} {R : ℝ}
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) (F : ℝ → ℝ) :
    (∫ θ : Angle, F θ ∂(radialMeasure v R hv hR : Measure Angle)) =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        v (circleMap 0 R θ) * F θ := by
  rw [radialMeasure, integral_densityMeasure _ _ (radialDensity_nonneg hv hR hn)]
  simp only [RadialDensity, ContinuousMap.coe_mk, mul_assoc]
  rw [integral_const_mul]
  exact congrArg ((2 * Real.pi)⁻¹ * ·)
    (integral_angle (fun θ => v (circleMap 0 R θ) * F θ))

theorem mass_radialMeasure {v : ℂ → ℝ} {R : ℝ}
    (hv : HarmonicOnNhd v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) :
    ((radialMeasure v R hv.continuousOn hR).mass : ℝ) = v 0 := by
  have h := integral_radialMeasure hv.continuousOn hR hn (fun _ => 1)
  have hr : HarmonicOnNhd v (closedBall 0 |R|) := by
    rw [abs_of_pos hR.1]
    exact hv.mono (closedBall_subset_ball hR.2)
  have hr' := hr.circleAverage_eq
  rw [Real.circleAverage_def] at hr'
  simp only [smul_eq_mul] at hr'
  simpa only [integral_const, smul_eq_mul, mul_one, FiniteMeasure.measureReal_eq_coe_coeFn,
    FiniteMeasure.mass, hr'] using h

theorem continuous_radialKernel (w : ℂ) :
    Continuous (fun R : Ioi ‖w‖ => radialKernel w R R.property) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hn (p : Ioi ‖w‖ × Angle) : circleMap 0 p.1 p.2 - w ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_circleMap_zero,
      abs_of_pos (lt_of_le_of_lt (norm_nonneg w) p.1.property)] at he
    exact (ne_of_gt p.1.property) he
  simp only [Function.uncurry_def, radialKernel, ContinuousMap.coe_mk,
    herglotzRieszKernel, sub_zero]
  apply Complex.continuous_re.comp
  apply Continuous.div _ _ hn <;> unfold circleMap <;> fun_prop

theorem integral_radialKernel {v : ℂ → ℝ} {R : ℝ}
    (hv : HarmonicOnNhd v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {w : ℂ} (hw : ‖w‖ < R) :
    (∫ θ : Angle, radialKernel w R hw θ
      ∂(radialMeasure v R hv.continuousOn hR : Measure Angle)) = v w := by
  have hr : HarmonicOnNhd v (closedBall 0 R) :=
    hv.mono (closedBall_subset_ball hR.2)
  have hp := hr.circleAverage_re_herglotzRieszKernel_smul
    (by simpa only [mem_ball, dist_zero_right] using hw)
  rw [Real.circleAverage_def] at hp
  change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 R θ)).re
    ∂(radialMeasure v R hv.continuousOn hR : Measure Angle)) = _
  rw [integral_radialMeasure hv.continuousOn hR hn
    (fun θ => (herglotzRieszKernel 0 w (circleMap 0 R θ)).re)]
  simpa only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.mul_apply, mul_comm] using hp

theorem approachRadius_tendsto : Tendsto approachRadius atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  simpa only [Function.comp_apply, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hn)

theorem continuous_clippedKernel (w : ℂ) (hw : ‖w‖ < 1) :
    Continuous (clippedKernel w hw) := by
  exact (continuous_radialKernel w).comp
    (show Continuous (clippedRadius w hw) from
      (continuous_const.max continuous_id).subtype_mk _)

theorem clippedKernel_one (w : ℂ) (hw : ‖w‖ < 1) :
    clippedKernel w hw 1 = radialKernel w 1 hw := by
  have ha : (‖w‖ + 1) / 2 ≤ 1 := by linarith
  simp only [clippedKernel, clippedRadius, max_eq_right ha]

theorem clippedKernel_eq {w : ℂ} (hw : ‖w‖ < 1) {R : ℝ}
    (hR : (‖w‖ + 1) / 2 < R) :
    clippedKernel w hw R = radialKernel w R (by linarith) := by
  simp only [clippedKernel, clippedRadius, max_eq_right hR.le]

theorem exists_radialSequence_cluster {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) :
    ∃ μ : FiniteMeasure Angle, (μ.mass : ℝ) = v 0 ∧
      MapClusterPt μ atTop (radialSequence v hv) := by
  let C : ℝ≥0 := ⟨v 0, hn 0 (by simp)⟩
  have hmass (n : ℕ) : (radialSequence v hv n).mass = C := by
    apply NNReal.coe_injective
    exact mass_radialMeasure hv (approachRadius_mem n) hn
  obtain ⟨μ, hμmass, hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace Angle C).exists_mapClusterPt
      (u := radialSequence v hv) (f := atTop) (by
        rw [Filter.le_principal_iff]
        change ∀ᶠ n : ℕ in atTop, (radialSequence v hv n).mass = C
        exact Eventually.of_forall hmass)
  exact ⟨μ, congrArg ((↑) : ℝ≥0 → ℝ) hμmass, hcluster⟩

theorem eventually_integral_clippedKernel {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {w : ℂ} (hw : ‖w‖ < 1) :
    ∀ᶠ n : ℕ in atTop,
      (∫ θ : Angle, clippedKernel w hw (approachRadius n) θ
        ∂(radialSequence v hv n : Measure Angle)) = v w := by
  have ha : (‖w‖ + 1) / 2 < 1 := by linarith
  filter_upwards [approachRadius_tendsto.eventually (Ioi_mem_nhds ha)] with n hn'
  have hwr : ‖w‖ < approachRadius n := by linarith
  rw [clippedKernel_eq hw hn']
  exact integral_radialKernel hv (approachRadius_mem n) hn hwr

theorem radialCluster_represents {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {μ : FiniteMeasure Angle}
    (hcluster : MapClusterPt μ atTop (radialSequence v hv))
    {w : ℂ} (hw : ‖w‖ < 1) :
    (∫ θ : Angle, radialKernel w 1 hw θ ∂(μ : Measure Angle)) = v w := by
  let l := comap (radialSequence v hv) (𝓝 μ) ⊓ (atTop : Filter ℕ)
  have : l.NeBot := neBot_inf_comap_iff_map'.mpr hcluster
  have hμ : Tendsto (radialSequence v hv) l (𝓝 μ) := tendsto_comap.mono_left inf_le_left
  have hR : Tendsto approachRadius l (𝓝 1) := approachRadius_tendsto.mono_left inf_le_right
  have hk : Tendsto (fun n => clippedKernel w hw (approachRadius n)) l
      (𝓝 (radialKernel w 1 hw)) := by
    simpa only [clippedKernel_one, Function.comp_def] using
      (continuous_clippedKernel w hw).continuousAt.tendsto.comp hR
  have hi := tendsto_integral_varying hμ hk
  have heq : ∀ᶠ n : ℕ in l,
      (∫ θ : Angle, clippedKernel w hw (approachRadius n) θ
        ∂(radialSequence v hv n : Measure Angle)) = v w :=
    (show l ≤ atTop from inf_le_right) (eventually_integral_clippedKernel hv hn hw)
  exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq))

theorem diskKernel_integrable (μ : FiniteMeasure Angle) {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun θ : Angle => herglotzRieszKernel 0 w (circleMap 0 1 θ))
      (μ : Measure Angle) :=
  (diskKernel w hw).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem hasDerivAt_diskIntegral (μ : FiniteMeasure Angle) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (diskIntegral μ)
      (∫ θ : Angle, 2 * circleMap 0 1 θ / (circleMap 0 1 θ - w) ^ 2
        ∂(μ : Measure Angle)) w := by
  let d := (1 - ‖w‖) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdist (x : ℂ) (hx : x ∈ ball w d) (θ : Angle) : d ≤ ‖circleMap 0 1 θ - x‖ := by
    have hnorm := norm_le_norm_sub_add x w
    have hx' : ‖x - w‖ < d := by simpa only [mem_ball, dist_eq_norm] using hx
    have he := norm_sub_norm_le (circleMap 0 1 θ) x
    simp only [norm_circleMap_zero, abs_one] at he
    dsimp [d] at *
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x (θ : Angle) => herglotzRieszKernel 0 x (circleMap 0 1 θ))
    (F' := fun x (θ : Angle) => 2 * circleMap 0 1 θ / (circleMap 0 1 θ - x) ^ 2)
    (bound := fun _ => 2 * (d ^ 2)⁻¹) (μ := (μ : Measure Angle))
    (ball_mem_nhds w hd) ?_ (diskKernel_integrable μ hw) ?_ ?_ (integrable_const _) ?_).2
  · filter_upwards with x
    simp only [herglotzRieszKernel, sub_zero, circleMap]
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards with θ x hx
    rw [norm_div, norm_mul, norm_pow, norm_circleMap_zero, abs_one, mul_one,
      show ‖(2 : ℂ)‖ = 2 by norm_num, div_eq_mul_inv]
    gcongr
    exact hdist x hx θ
  · filter_upwards with θ x hx
    have hne : circleMap 0 1 θ - x ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le hd (hdist x hx θ))
    have hh := ((hasDerivAt_id' x).const_add (circleMap 0 1 θ)).div
      ((hasDerivAt_id' x).const_sub (circleMap 0 1 θ)) hne
    simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using hh

theorem analyticOnNhd_diskIntegral (μ : FiniteMeasure Angle) :
    AnalyticOnNhd ℂ (diskIntegral μ) (ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro w hw
  exact (hasDerivAt_diskIntegral μ (by simpa only [mem_ball, dist_zero_right] using hw)).differentiableAt.differentiableWithinAt

theorem add_I_ne_zero {s : ℂ} (hs : 0 < s.im) : s + I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  linarith

theorem one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hw

theorem norm_toDisk_lt_one {s : ℂ} (hs : 0 < s.im) : ‖toDisk s‖ < 1 := by
  have hd := add_I_ne_zero hs
  rw [toDisk, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.I_re, sub_zero,
    Complex.add_re, add_zero, Complex.sub_im, Complex.add_im, Complex.I_im]
  nlinarith

theorem im_toHalfPlane (w : ℂ) :
    (toHalfPlane w).im = (1 - ‖w‖ ^ 2) / Complex.normSq (1 - w) := by
  simp only [toHalfPlane, Complex.div_im, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    zero_mul, one_mul, zero_add, zero_sub, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  ring

theorem im_toHalfPlane_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (toHalfPlane w).im := by
  rw [im_toHalfPlane]
  apply div_pos _ (Complex.normSq_pos.mpr (one_sub_ne_zero hw))
  nlinarith [norm_nonneg w]

theorem toHalfPlane_toDisk {s : ℂ} (hs : 0 < s.im) : toHalfPlane (toDisk s) = s := by
  have hd := add_I_ne_zero hs
  have he := one_sub_ne_zero (norm_toDisk_lt_one hs)
  dsimp [toHalfPlane, toDisk] at *
  field_simp
  ring

theorem analyticAt_toHalfPlane {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ toHalfPlane w := by
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero hw)

theorem continuous_weighted_radial {v : ℂ → ℝ}
    (hv : ContinuousOn v (ball 0 1)) (f : C(Angle, ℝ))
    (hc : ∀ θ ∈ tsupport f, ContinuousAt v (circleMap 0 1 θ)) :
    Continuous (fun p : Icc (0 : ℝ) 1 × Angle =>
      f p.2 * v (circleMap 0 p.1 p.2)) := by
  have hm : Continuous (fun p : Icc (0 : ℝ) 1 × Angle => circleMap 0 p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hf : p.2 ∈ tsupport f
  · apply (f.continuous.comp continuous_snd).continuousAt.mul
    apply ContinuousAt.comp _ hm.continuousAt
    rcases lt_or_eq_of_le p.1.property.2 with hr | hr
    · apply hv.continuousAt (isOpen_ball.mem_nhds _)
      simp only [mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg p.1.property.1]
      exact hr
    · simpa only [hr] using hc p.2 hf
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    have he := (notMem_tsupport_iff_eventuallyEq.mp hf).comp_tendsto
      (continuous_snd.continuousAt : ContinuousAt Prod.snd p)
    filter_upwards [he] with q hq
    simp only [Function.comp_apply, Pi.zero_apply] at hq
    simp [hq]

theorem tendsto_radial_test_zero {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) (f : C(Angle, ℝ))
    (hc : ∀ θ ∈ tsupport f, ContinuousAt v (circleMap 0 1 θ))
    (hz : ∀ θ ∈ tsupport f, v (circleMap 0 1 θ) = 0) :
    Tendsto (fun n => ∫ θ : Angle, f θ ∂(radialSequence v hv n : Measure Angle))
      atTop (𝓝 0) := by
  let R : ℕ → Icc (0 : ℝ) 1 := fun n =>
    ⟨approachRadius n, (approachRadius_mem n).1.le, (approachRadius_mem n).2.le⟩
  let R₁ : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hR : Tendsto R atTop (𝓝 R₁) := tendsto_subtype_rng.mpr approachRadius_tendsto
  have hj := continuous_weighted_radial hv.continuousOn f hc
  let F : Icc (0 : ℝ) 1 → C(Angle, ℝ) := fun r =>
    ⟨fun θ => f θ * v (circleMap 0 r θ), hj.comp (continuous_const.prodMk continuous_id)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hj
  have hF₁ : F R₁ = 0 := by
    ext θ
    change f θ * v (circleMap 0 1 θ) = 0
    by_cases he : f θ = 0
    · simp [he]
    · simp [hz θ (subset_closure he)]
  have ht : Tendsto (fun n => F (R n)) atTop (𝓝 0) := by
    simpa only [hF₁, Function.comp_def] using hF.continuousAt.tendsto.comp hR
  let μV : FiniteMeasure Angle := ⟨volume, inferInstance⟩
  have hi := tendsto_integral_varying (tendsto_const_nhds (x := μV)) ht
  change Tendsto (fun n => ∫ θ : Angle, F (R n) θ) atTop (𝓝 (∫ θ : Angle, (0 : C(Angle, ℝ)) θ)) at hi
  have he (n : ℕ) :
      (∫ θ : Angle, f θ ∂(radialSequence v hv n : Measure Angle)) =
        (2 * Real.pi)⁻¹ * ∫ θ : Angle, F (R n) θ := by
    change (∫ θ : Angle, f θ ∂(densityMeasure (volume : Measure Angle)
      (RadialDensity v (approachRadius n) hv.continuousOn (approachRadius_mem n)) : Measure Angle)) = _
    rw [integral_densityMeasure _ _
      (radialDensity_nonneg hv.continuousOn (approachRadius_mem n) hn)]
    simp only [RadialDensity, ContinuousMap.coe_mk, mul_assoc]
    rw [integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with θ
    change v (circleMap 0 (approachRadius n) θ) * f θ =
      f θ * v (circleMap 0 (approachRadius n) θ)
    ring
  simpa only [he, ContinuousMap.zero_apply, integral_zero, mul_zero] using
    hi.const_mul ((2 * Real.pi)⁻¹)

theorem radialCluster_integral_zero {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {μ : FiniteMeasure Angle}
    (hcluster : MapClusterPt μ atTop (radialSequence v hv)) (f : C(Angle, ℝ))
    (hc : ∀ θ ∈ tsupport f, ContinuousAt v (circleMap 0 1 θ))
    (hz : ∀ θ ∈ tsupport f, v (circleMap 0 1 θ) = 0) :
    (∫ θ : Angle, f θ ∂(μ : Measure Angle)) = 0 := by
  let l := comap (radialSequence v hv) (𝓝 μ) ⊓ (atTop : Filter ℕ)
  have : l.NeBot := neBot_inf_comap_iff_map'.mpr hcluster
  have hμ : Tendsto (radialSequence v hv) l (𝓝 μ) := tendsto_comap.mono_left inf_le_left
  exact tendsto_nhds_unique
    ((FiniteMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp hμ)
    ((tendsto_radial_test_zero hv hn f hc hz).mono_left inf_le_right)

theorem radialCluster_no_mass {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {μ : FiniteMeasure Angle}
    (hcluster : MapClusterPt μ atTop (radialSequence v hv))
    {U : Set Angle} (hU : IsOpen U)
    (hc : ∀ θ ∈ U, ContinuousAt v (circleMap 0 1 θ))
    (hz : ∀ θ ∈ U, v (circleMap 0 1 θ) = 0) : (μ : Measure Angle) U = 0 := by
  have hs : U ⊆ (μ : Measure Angle).supportᶜ := by
    intro θ hθ
    obtain ⟨f, hfU, hfθ, hfr⟩ := exists_tsupport_one_of_isOpen_isClosed hU
      isClosed_closure.isCompact isClosed_singleton (singleton_subset_iff.mpr hθ)
    have hzero : (∫ z : Angle, f z ∂(μ : Measure Angle)) = 0 :=
      radialCluster_integral_zero hv hn hcluster f
        (fun z hz' => hc z (hfU hz')) (fun z hz' => hz z (hfU hz'))
    have hae : f =ᵐ[(μ : Measure Angle)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => (hfr z).1)
        (f.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).mp hzero
    apply Measure.notMem_support_iff_exists.mpr
    refine ⟨{z | f z ≠ 0}, ?_, ?_⟩
    · exact f.continuous.continuousAt.eventually_ne (by simp [hfθ (mem_singleton θ)])
    · exact ae_iff.mp hae
  exact measure_mono_null hs (Measure.measure_compl_support (μ := (μ : Measure Angle)))

theorem positive_real_disk_representation_with_support {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (ball 0 1))
    (hn : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (P w).re)
    {U : Set Angle} (hU : IsOpen U)
    (hc : ∀ θ ∈ U, ContinuousAt (fun w => (P w).re) (circleMap 0 1 θ))
    (hz : ∀ θ ∈ U, (P (circleMap 0 1 θ)).re = 0) :
    ∃ (μ : FiniteMeasure Angle) (c : ℝ), (μ : Measure Angle) U = 0 ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        P w = (c : ℂ) * I + diskIntegral μ w := by
  have hh : HarmonicOnNhd (fun w => (P w).re) (ball 0 1) :=
    fun w hw => (hP w hw).harmonicAt_re
  obtain ⟨μ, _, hcluster⟩ := exists_radialSequence_cluster hh hn
  have hre (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : (P w - diskIntegral μ w).re = 0 := by
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    have hi := Complex.reCLM.integral_comp_comm (diskKernel_integrable μ hwn)
    change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re
      ∂(μ : Measure Angle)) = (diskIntegral μ w).re at hi
    have hr := radialCluster_represents hh hn hcluster hwn
    change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re
      ∂(μ : Measure Angle)) = (P w).re at hr
    rw [Complex.sub_re, ← hi, hr, sub_self]
  obtain ⟨c, hcc⟩ := (hP.sub (analyticOnNhd_diskIntegral μ)).eq_re_add_const_mul_I_of_re_eq_const
    hre isOpen_ball (isConnected_ball (by norm_num))
  refine ⟨μ, c, radialCluster_no_mass hh hn hcluster hU hc hz, fun w hw => ?_⟩
  have he := hcc w hw
  simp only [Complex.ofReal_zero, zero_add] at he
  exact sub_eq_iff_eq_add.mp he

theorem re_toHalfPlane (w : ℂ) :
    (toHalfPlane w).re = -2 * w.im / Complex.normSq (1 - w) := by
  simp only [toHalfPlane, Complex.div_re, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    zero_mul, one_mul, zero_add, zero_sub]
  ring

theorem one_sub_ne_zero_of_im_neg {w : ℂ} (hw : w.im < 0) : 1 - w ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.one_im, Complex.zero_im, zero_sub] at hh
  linarith

theorem boundary_toHalfPlane {w : ℂ} (hw : ‖w‖ = 1) (hi : w.im < 0) :
    (toHalfPlane w).im = 0 ∧ 0 < (toHalfPlane w).re := by
  constructor
  · simp [im_toHalfPlane, hw]
  · rw [re_toHalfPlane]
    exact div_pos (mul_pos_of_neg_of_neg (by norm_num) hi)
      (Complex.normSq_pos.mpr (one_sub_ne_zero_of_im_neg hi))

theorem analyticAt_toHalfPlane_of_ne {w : ℂ} (hw : 1 - w ≠ 0) :
    AnalyticAt ℂ toHalfPlane w := by
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hw

theorem upper_half_plane_representation_with_support_of_continuous {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → ContinuousAt P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ (μ : FiniteMeasure Angle) (a : ℝ),
      (∀ᵐ θ : Angle ∂(μ : Measure Angle), 0 ≤ (circleMap 0 1 θ).im) ∧
      ∀ s : ℂ, 0 < s.im → P s = (a : ℂ) + I * diskIntegral μ (toDisk s) := by
  let Q : ℂ → ℂ := fun w => -I * P (toHalfPlane w)
  have hQ : AnalyticOnNhd ℂ Q (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    exact analyticAt_const.mul ((hP _ (im_toHalfPlane_pos hwn)).comp
      (analyticAt_toHalfPlane hwn))
  have hQn : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (Q w).re := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    simpa [Q, Complex.mul_re] using hn _ (im_toHalfPlane_pos hwn)
  let U : Set Angle := {θ | (circleMap 0 1 θ).im < 0}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hboundary (θ : Angle) (hθ : θ ∈ U) :
      ContinuousAt (fun w => (Q w).re) (circleMap 0 1 θ) ∧
        (Q (circleMap 0 1 θ)).re = 0 := by
    have hb := boundary_toHalfPlane (w := circleMap 0 1 θ)
      (by simp only [norm_circleMap_zero, abs_one]) hθ
    have he : ((toHalfPlane (circleMap 0 1 θ)).re : ℂ) = toHalfPlane (circleMap 0 1 θ) := by
      simpa only [hb.1, Complex.ofReal_zero, zero_mul, add_zero] using
        Complex.re_add_im (toHalfPlane (circleMap 0 1 θ))
    have hp := hR _ hb.2
    rw [he] at hp
    constructor
    · refine Complex.continuous_re.continuousAt.comp ?_
      change ContinuousAt Q (circleMap 0 1 θ)
      exact continuousAt_const.mul (hp.1.comp
        (analyticAt_toHalfPlane_of_ne (one_sub_ne_zero_of_im_neg hθ)).continuousAt)
    · simpa [Q, Complex.mul_re] using hp.2
  obtain ⟨μ, c, hm, hc⟩ := positive_real_disk_representation_with_support hQ hQn hU
    (fun θ hθ => (hboundary θ hθ).1) (fun θ hθ => (hboundary θ hθ).2)
  refine ⟨μ, -c, ?_, fun s hs => ?_⟩
  · have ha := measure_eq_zero_iff_ae_notMem.mp hm
    filter_upwards [ha] with θ hθ
    exact le_of_not_gt hθ
  · have he := hc (toDisk s) (by simpa only [mem_ball, dist_zero_right] using norm_toDisk_lt_one hs)
    dsimp [Q] at he
    rw [toHalfPlane_toDisk hs] at he
    have ht := congrArg (I * ·) he
    simpa [mul_add, mul_neg, ← mul_assoc, mul_comm I (c : ℂ),
      mul_assoc (c : ℂ) I I, Complex.I_sq] using ht

theorem boundaryWeight_pos (θ : Angle) : 0 < boundaryWeight θ := by
  dsimp [boundaryWeight]
  positivity

theorem boundaryWeight_le_one (θ : Angle) : boundaryWeight θ ≤ 1 := by
  dsimp [boundaryWeight]
  exact inv_le_one_of_one_le₀ (by linarith [le_max_left 0 (circleMap 0 1 θ).im])

theorem compactKernel_boundary {s ζ : ℂ} (hs : 0 < s.im)
    (hζ : ‖ζ‖ = 1) (hi : 0 ≤ ζ.im) :
    I * herglotzRieszKernel 0 (toDisk s) ζ =
      (1 - 2 * ((1 - ζ.re + ζ.im) / (2 * (1 + ζ.im)) : ℝ) : ℂ) +
      (s - 1) * compactKernel ((1 - ζ.re + ζ.im) / (2 * (1 + ζ.im)))
        (1 + ζ.im)⁻¹ s := by
  have hsi := add_I_ne_zero hs
  have hd : ζ - toDisk s ≠ 0 := by
    intro h
    have he : ζ = toDisk s := sub_eq_zero.mp h
    have := norm_toDisk_lt_one hs
    rw [← he, hζ] at this
    exact (lt_irrefl _ this).elim
  have hnorm : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, Complex.sq_norm, hζ, pow_two] using Complex.normSq_eq_norm_sq ζ
  have hp : 0 < 2 * (1 + ζ.im) := by positivity
  have hr : |ζ.re| ≤ 1 := hζ ▸ Complex.abs_re_le_norm ζ
  have ht : (1 - ζ.re + ζ.im) / (2 * (1 + ζ.im)) ∈ Icc (0 : ℝ) 1 := by
    rw [abs_le] at hr
    exact ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩
  have hden := compactDen_ne_zero ht (Or.inl hs)
  have hc : (2 * (1 + (ζ.im : ℂ))) ≠ 0 := by
    exact_mod_cast hp.ne'
  have hc' : 1 + (ζ.im : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + ζ.im ≠ 0)
  simp only [herglotzRieszKernel_def, sub_zero, compactKernel, toDisk,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_inv] at *
  have hd₂ : ζ * (s + I) - (s - I) ≠ 0 := by
    intro he
    apply hd
    apply sub_eq_zero.mpr
    apply (eq_div_iff hsi).mpr
    exact sub_eq_zero.mp he
  have hd₃ : 2 * (1 + (ζ.im : ℂ)) + (1 - ζ.re + ζ.im) * (s - 1) ≠ 0 := by
    intro he
    apply hden
    field_simp [hc', hc]
    linear_combination he
  field_simp [hsi, hd₂, hd₃, hc, hc']
  apply Complex.ext <;> norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.add_im, Complex.sub_im, Complex.mul_im]
  all_goals grind only

theorem compactKernel_integrable (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) :
    Integrable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s)
      (μ : Measure Angle) := by
  have hc : Continuous (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
    exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_boundaryParameter)))
      (fun θ => compactDen_ne_zero (boundaryParameter_mem θ) hs)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem compactKernel_norm_le_two {s : ℂ} (hs : ‖s - 1‖ < 1 / 2) (θ : Angle) :
    ‖compactKernel (boundaryParameter θ) (boundaryWeight θ) s‖ ≤ 2 := by
  have ht := boundaryParameter_mem θ
  have htw := boundaryWeight_le_one θ
  have htp := boundaryWeight_pos θ
  have ht' : ‖(boundaryParameter θ : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hsmall : ‖(s - 1) * (boundaryParameter θ : ℂ)‖ < 1 / 2 := by
    rw [norm_mul]
    calc
      ‖s - 1‖ * ‖(boundaryParameter θ : ℂ)‖ ≤ ‖s - 1‖ * 1 := mul_le_mul_of_nonneg_left ht' (norm_nonneg _)
      _ < 1 / 2 := by simpa using hs
  have hden : 1 / 2 < ‖1 + (s - 1) * (boundaryParameter θ : ℂ)‖ := by
    have he := norm_sub_norm_le (1 : ℂ) (-((s - 1) * (boundaryParameter θ : ℂ)))
    simp only [norm_one, norm_neg, sub_neg_eq_add] at he
    linarith
  rw [compactKernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 + (s - 1) * (boundaryParameter θ : ℂ)‖)).mpr
  linarith

theorem continuousAt_compactIntegral_one (μ : FiniteMeasure Angle) :
    ContinuousAt (compactIntegral μ) 1 := by
  apply continuousAt_of_dominated (bound := fun _ => 2)
  · filter_upwards with s
    have hm : Measurable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
      unfold compactKernel
      exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).measurable.div
        (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).measurable
    exact hm.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    filter_upwards with θ
    exact compactKernel_norm_le_two (by simpa only [mem_ball, dist_eq_norm] using hs) θ
  · exact integrable_const _
  · filter_upwards with θ
    apply ContinuousAt.div continuousAt_const
      (continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))
    simp

theorem pick_divided_difference_of_continuous {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → ContinuousAt P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ μ : FiniteMeasure Angle, ∀ s : ℂ, 0 < s.im →
      P s - P 1 = (s - 1) * compactIntegral μ s := by
  obtain ⟨μ, a, hμ, hrep⟩ := upper_half_plane_representation_with_support_of_continuous hP hn hR
  let A : ℂ := (a : ℂ) + ∫ θ : Angle, (1 - 2 * (boundaryParameter θ : ℂ)) ∂(μ : Measure Angle)
  have hiA : Integrable (fun θ : Angle => (1 - 2 * (boundaryParameter θ : ℂ))) (μ : Measure Angle) :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_boundaryParameter))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (s : ℂ) (hs : 0 < s.im) : P s = A + (s - 1) * compactIntegral μ s := by
    rw [hrep _ hs, diskIntegral, ← integral_const_mul]
    have heq : (fun θ : Angle => I * herglotzRieszKernel 0 (toDisk s) (circleMap 0 1 θ)) =ᵐ[(μ : Measure Angle)]
        (fun θ : Angle => (1 - 2 * (boundaryParameter θ : ℂ)) +
          (s - 1) * compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
      filter_upwards [hμ] with θ hθ
      simpa only [boundaryParameter, boundaryWeight, max_eq_right hθ] using
        compactKernel_boundary hs (by simp only [norm_circleMap_zero, abs_one]) hθ
    rw [integral_congr_ae heq, integral_add hiA ((compactKernel_integrable μ (Or.inl hs)).const_mul _),
      integral_const_mul]
    exact (add_assoc _ _ _).symm
  have hlim : Tendsto (fun n : ℕ => (1 : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (1 : ℝ))).sub approachRadius_tendsto)).mul_const I)
  have hseq (n : ℕ) : 0 < ((1 : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I).im := by
    simpa using sub_pos.mpr (approachRadius_mem n).2
  have hA : P 1 = A := by
    have hleft := (hR 1 (by norm_num)).1.tendsto.comp hlim
    have hright := (tendsto_const_nhds (x := A)).add
      ((hlim.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul ((continuousAt_compactIntegral_one μ).tendsto.comp hlim))
    simp only [sub_self, zero_mul, add_zero] at hright
    exact tendsto_nhds_unique hleft (hright.congr (fun n => (he _ (hseq n)).symm))
  exact ⟨μ, fun s hs => by rw [he s hs, hA]; ring⟩

end EntropyPhotonNumber.Herglotz

end

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Herglotz
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
attribute [local instance] OAI.EntropyPhotonNumber.Herglotz.instMeasureSpaceElemRealAngle


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.Herglotz.pick_divided_difference_of_continuous := @_root_.OAI.EntropyPhotonNumber.Herglotz.pick_divided_difference_of_continuous
