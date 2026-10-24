-- Prove2me | solution 1 for OAI.CenteredDiskEndpoint.main_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T21:40:32.122101+00:00
-- url     : https://prove2.me/submissions/8c11490d-3aa4-486c-ba56-2a95739e5c66

import Mathlib
import Definitions.Def_DiskMaximal
import Definitions.Def_OAIQWCDE000
import Theorems.Thm_OAI_SobolevBand_smooth_dyadic_bound

section
-- module Solutions.OAIQW_DiskMaximal.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace CenteredDiskEndpoint

/-- The normalization is precisely planar Lebesgue disk area. -/
theorem volume_disk (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul Real.pi_nonneg,
    ENNReal.ofReal_pow hr]
  exact mul_comm _ _

/-- For every admissible input and positive radius the extended average agrees
with the real absolute-value average, rather than a signed average. -/
theorem absoluteDiskAverage_eq_ofReal {f : Plane → ℝ} {x : Plane} {r : ℝ}
    (hf : IntegrableOn f (Metric.ball x r)) (hr : 0 < r) :
    absoluteDiskAverage f x r = ENNReal.ofReal (diskAverage (fun y => |f y|) x r) := by
  have hden : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  rw [absoluteDiskAverage, diskAverage, ENNReal.ofReal_div_of_pos hden,
    ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun y => abs_nonneg (f y)))]

theorem inW11Loc_of_gradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) (hw : HasWeakGradient f g) : InW11Loc f :=
  ⟨hf, g, hg.locallyIntegrable, hw⟩

end CenteredDiskEndpoint

open scoped RealInnerProductSpace

namespace CenteredDiskEndpoint
open Filter

/-- Spherical boundaries are null, so the choice of an open disk does not alter
Lebesgue differentiation averages. -/
theorem disk_ae_eq_closedDisk (x : Plane) (r : ℝ) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
  · exact (Measure.addHaar_closedBall_eq_addHaar_ball volume x r).le
  · exact measurableSet_ball.nullMeasurableSet
  · exact measure_closedBall_lt_top.ne

theorem average_closedDisk_eq (f : Plane → ℝ) (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (⨍ y in Metric.closedBall x r, f y) = diskAverage f x r := by
  rw [← setAverage_congr (disk_ae_eq_closedDisk x r), setAverage_eq,
    diskAverage, measureReal_def, volume_disk x hr, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul, div_eq_inv_mul]

/-- Almost every point is a Lebesgue point for absolute disk averages. -/
theorem ae_tendsto_diskAverage_abs {f : Plane → ℝ} (hf : Integrable f) :
    ∀ᵐ x, Tendsto (fun r => diskAverage (fun y => |f y|) x r)
      (𝓝[>] (0 : ℝ)) (𝓝 |f x|) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hf.abs.locallyIntegrable 0]
    with x hx
  have h := hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    (Eventually.of_forall (fun r => by simp))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact average_closedDisk_eq (fun y => |f y|) x hr.le

/-- Away from zero the denominator alone bounds all absolute averages. -/
theorem diskAverage_abs_le_of_radius_le {f : Plane → ℝ} (hf : Integrable f)
    (x : Plane) {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    diskAverage (fun y => |f y|) x r ≤ (∫ y, |f y|) / (Real.pi * a ^ 2) := by
  have hr : 0 < r := ha.trans_le har
  have hnum : (∫ y in Metric.ball x r, |f y|) ≤ ∫ y, |f y| :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun y => abs_nonneg (f y))) hf.abs
  have hden : Real.pi * a ^ 2 ≤ Real.pi * r ^ 2 :=
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ ha.le hr.le).2 har) Real.pi_nonneg
  dsimp [diskAverage]
  calc
    (∫ y in Metric.ball x r, |f y|) / (Real.pi * r ^ 2) ≤
        (∫ y, |f y|) / (Real.pi * r ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (∫ y, |f y|) / (Real.pi * a ^ 2) :=
      div_le_div_of_nonneg_left (integral_nonneg (fun y => abs_nonneg (f y)))
        (by positivity) hden

/-- A genuine clause of the endpoint, in fact valid for every L¹ input. No
maximal bound, gradient hypothesis, or selected radius is used here. -/
theorem ae_maximal_ne_top {f : Plane → ℝ} (hf : Integrable f) :
    ∀ᵐ x, maximal f x ≠ ⊤ := by
  filter_upwards [ae_tendsto_diskAverage_abs hf] with x hx
  obtain ⟨C, hC⟩ := hx.isBoundedUnder_le
  obtain ⟨a, ha, haC⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hC
  have hbound (r : ℝ) (hr : 0 < r) :
      diskAverage (fun y => |f y|) x r ≤ max C ((∫ y, |f y|) / (Real.pi * a ^ 2)) := by
    by_cases hra : r ≤ a
    · exact (haC ⟨hr, hra⟩).trans (le_max_left _ _)
    · exact (diskAverage_abs_le_of_radius_le hf x ha (le_of_not_ge hra)).trans
        (le_max_right _ _)
  have hmax : maximal f x ≤ ENNReal.ofReal
      (max C ((∫ y, |f y|) / (Real.pi * a ^ 2))) := by
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    rw [absoluteDiskAverage_eq_ofReal hf.integrableOn hr]
    exact ENNReal.ofReal_le_ofReal (hbound r hr)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmax

end CenteredDiskEndpoint

open MeasureTheory Set Filter
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff

noncomputable section

namespace DiskMoments

attribute [local instance] OAI.DiskMoments.instFactEqNatFinrankRealComplexOfNat_solutions
lemma integral_translate_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (x : ℂ) (r : ℝ) :
    (∫ z in Metric.ball 0 r, f (x + z)) = ∫ y in Metric.ball x r, f y := by
  have hpre : (fun z : ℂ => x + z) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext z
    simp [Metric.mem_ball, dist_eq_norm]
  have h := (measurePreserving_add_left volume x).setIntegral_preimage_emb
    (Homeomorph.addLeft x).measurableEmbedding f (Metric.ball x r)
  rwa [hpre] at h

lemma continuous_gradient {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (gradient g) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hg.continuous_fderiv one_ne_zero)

lemma real_moment_integrand (g : ℂ → ℝ) (x z : ℂ) :
    (star z * gradient g x).re = (fderiv ℝ g x) z := by
  rw [← inner_gradient_left, Complex.inner]
  simp [mul_comm]

/-- Differentiate a disk average on its fixed unit-disk model. -/
theorem hasDerivAt_integral_unitDisk {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1, g (x + s • z))
      (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x + t • z)) z) t := by
  let F : ℝ → ℂ → ℝ := fun s z => g (x + s • z)
  let F' : ℝ → ℂ → ℝ := fun s z => (fderiv ℝ g (x + s • z)) z
  have hdc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (|t|+1)).exists_bound_of_continuousOn hdc.continuousOn
  have hFm (s : ℝ) : Continuous (F s) := hg.continuous.comp (by fun_prop)
  have hF'm (s : ℝ) : Continuous (F' s) := by
    unfold F'
    exact (hdc.comp (by fun_prop)).clm_apply continuous_id
  have hFi : IntegrableOn (F t) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1) (hFm t).continuousOn).mono_set
      Metric.ball_subset_closedBall
  have hdiff (z : ℂ) (s : ℝ) : HasDerivAt (fun s => F s z) (F' s z) s := by
    convert! ((hg.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).smul_const z).const_add x)) using 1
    simp [F', id_eq]
  have hbound : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      ∀ s ∈ Metric.ball t 1, ‖F' s z‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz s hs
    have hz' : ‖z‖ ≤ 1 := by simpa [Metric.mem_ball, dist_zero_right] using
      (show ‖z‖ < 1 by simpa [Metric.mem_ball, dist_zero_right] using hz).le
    have hs' : |s| ≤ |t| + 1 := by
      have hh : |s-t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hs
      have hh' := abs_add_le (s-t) t
      rw [sub_add_cancel] at hh'
      linarith
    have hpos : x + s • z ∈ Metric.closedBall x (|t|+1) := by
      simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hz' (abs_nonneg s)).trans (by simpa using hs')
    exact ((fderiv ℝ g (x+s•z)).le_opNorm _).trans
      (by simpa only [mul_one] using (mul_le_mul ((hC _ hpos).trans (le_max_left C 0)) hz'
        (norm_nonneg _) (le_max_right C 0)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Metric.ball (0 : ℂ) 1))
    (x₀ := t) (s := Metric.ball t 1) (F := F) (F' := F') (bound := fun _ => max C 0)
    (Metric.ball_mem_nhds _ zero_lt_one) (Filter.Eventually.of_forall (fun s => (hFm s).aestronglyMeasurable))
    hFi (hF'm t).aestronglyMeasurable hbound (integrableOn_const (by finiteness))
    (Filter.Eventually.of_forall (fun z s _ => hdiff z s))).2

lemma integral_scale_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, f (t • z)) =
      (t^2)⁻¹ • ∫ z in Metric.ball (0 : ℂ) t, f z := by
  convert Measure.setIntegral_comp_smul_of_pos volume f (Metric.ball 0 1) ht using 1
  rw [Complex.finrank_real_complex, smul_ball ht.ne', smul_zero, Real.norm_eq_abs, abs_of_pos ht, mul_one]

lemma signedAverage_fixedDomain (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage g x t = (∫ z in Metric.ball (0 : ℂ) 1, g (x + t • z)) / Real.pi := by
  rw [integral_scale_ball (fun z => g (x+z)) ht, integral_translate_ball]
  simp only [signedAverage, smul_eq_mul]
  ring

lemma integral_fderiv_scale (g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ z in Metric.ball (0 : ℂ) 1, (fderiv ℝ g (x+t•z)) z) =
      (t^3)⁻¹ * ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
  have hi (z : ℂ) : (fderiv ℝ g (x+t•z)) z =
      t⁻¹ * (fderiv ℝ g (x+t•z)) (t•z) := by
    rw [map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  simp_rw [hi]
  rw [integral_const_mul, integral_scale_ball (fun z => (fderiv ℝ g (x+z)) z) ht]
  have hh : (∫ z in Metric.ball (0 : ℂ) t, (fderiv ℝ g (x+z)) z) =
      ∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x) := by
    simpa using integral_translate_ball (fun y => (fderiv ℝ g y) (y-x)) x t
  rw [hh]
  simp only [smul_eq_mul]
  ring

lemma integral_fderiv_moment_real {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    (∫ y in Metric.ball x t, (fderiv ℝ g y) (y-x)) =
      (∫ y in Metric.ball x t, star (y-x) * gradient g y).re := by
  have hi : IntegrableOn (fun y => star (y-x) * gradient g y) (Metric.ball x t) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall x t)
      ((by fun_prop : Continuous (fun y : ℂ => star (y-x))).mul
        (continuous_gradient hg)).continuousOn).mono_set Metric.ball_subset_closedBall
  change _ = Complex.reCLM _
  rw [← Complex.reCLM.integral_comp_comm hi]
  congr 1
  funext y
  exact (real_moment_integrand g y (y-x)).symm

/-- The radial disk derivative is the real part of its complex moment. -/
theorem hasDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (signedAverage g x)
      ((∫ y in Metric.ball x t, star (y-x) * gradient g y).re / (Real.pi * t^3)) t := by
  have hd := (hasDerivAt_integral_unitDisk hg x t).div_const Real.pi
  rw [integral_fderiv_scale g x ht, integral_fderiv_moment_real hg x t] at hd
  have he : (fun s => (∫ z in Metric.ball (0 : ℂ) 1, g (x+s•z)) / Real.pi)
      =ᶠ[𝓝 t] signedAverage g x := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact (signedAverage_fixedDomain g x hs).symm
  convert! hd.congr_of_eventuallyEq he.symm using 1; try rfl
  ring

end DiskMoments

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

noncomputable section

namespace DiskMoments
open DiskKernels

lemma gradient_hasCompactSupport {g : ℂ → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (gradient g) := (hc.fderiv ℝ).comp_left (map_zero _)

end DiskMoments

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.MaximalEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace DiskMaximalTools

lemma volume_dilate_five (x : ℂ) (r : ℝ) :
    volume (ball x (5*r)) = 25 * volume (ball x r) := by
  rw [Complex.volume_ball, Complex.volume_ball, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num [mul_pow]
  ring

/-- The actual Vitali weak-(1,1) estimate, with no assumed maximal inequality. -/
theorem weak_bound_bounded_family {ι : Type*} (t : Set ι) (x : ι → ℂ) (r : ι → ℝ)
    (ν : Measure ℂ) {R a : ℝ} (ha : 0 < a)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (hav : ∀ i ∈ t, ENNReal.ofReal a * volume (ball (x i) (r i)) ≤ ν (ball (x i) (r i))) :
    volume (⋃ i ∈ t, ball (x i) (r i)) ≤ (25 / ENNReal.ofReal a) * ν univ := by
  obtain ⟨u,hut,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    t x r R hR 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun i hi => ⟨x i,mem_ball_self (hr i (hut hi))⟩)
  have : Countable u := huc.to_subtype
  have hsub : (⋃ i ∈ t, ball (x i) (r i)) ⊆ ⋃ i : u, ball (x i) (5*r i) := by
    intro y hy
    obtain ⟨i,hi,hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hij hy⟩
  have hmass : (∑' i : u, ν (ball (x i) (r i))) ≤ ν univ := by
    rw [← measure_iUnion (fun (i j : u) hij => hdisj i.property j.property (fun h => hij (Subtype.ext h)))
      (fun _ => measurableSet_ball)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ volume (⋃ i : u, ball (x i) (5*r i)) := measure_mono hsub
    _ ≤ ∑' i : u, volume (ball (x i) (5*r i)) := measure_iUnion_le _
    _ = ∑' i : u, 25 * volume (ball (x i) (r i)) := by simp_rw [volume_dilate_five]
    _ ≤ ∑' i : u, (25 / ENNReal.ofReal a) * ν (ball (x i) (r i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hb := hav i (hut i.property)
      calc
        _ = (25 / ENNReal.ofReal a) * (ENNReal.ofReal a * volume (ball (x i) (r i))) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top]
        _ ≤ _ := by gcongr
    _ = (25 / ENNReal.ofReal a) * ∑' i : u, ν (ball (x i) (r i)) := by rw [ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

lemma volume_disk_real (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [Complex.volume_ball,ENNReal.ofReal_mul Real.pi_nonneg,ENNReal.ofReal_pow hr]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  exact mul_comm _ _

/-- All high-average balls of a finite measure have a common finite radius
bound; the bounded-family Vitali argument therefore controls every radius. -/
theorem weak_bound {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x : ℂ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal a * volume (ball x r) ≤ ν (ball x r)} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  let t : Set (ℂ × ℝ) := {p | 0 < p.2 ∧
    ENNReal.ofReal a * volume (ball p.1 p.2) ≤ ν (ball p.1 p.2)}
  let B : ℝ := (ν univ).toReal/(a*Real.pi)
  have hB : 0 ≤ B := div_nonneg ENNReal.toReal_nonneg (mul_pos ha Real.pi_pos).le
  have hR : ∀ p ∈ t, p.2 ≤ B+1 := by
    intro p hp
    have hh := hp.2.trans (measure_mono (subset_univ _))
    rw [volume_disk_real _ hp.1.le,← ENNReal.ofReal_mul ha.le] at hh
    have hh' : a*(Real.pi*p.2^2) ≤ (ν univ).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hh
    have hs : p.2^2 ≤ B := (le_div_iff₀ (mul_pos ha Real.pi_pos)).mpr (by nlinarith)
    nlinarith [sq_nonneg (p.2-1)]
  have hweak := weak_bound_bounded_family t Prod.fst Prod.snd ν ha
    (fun _ hp => hp.1) hR (fun _ hp => hp.2)
  apply le_trans (measure_mono ?_) hweak
  intro x hx
  obtain ⟨r,hr,havg⟩ := hx
  exact mem_iUnion₂.mpr ⟨(x,r),⟨hr,havg⟩,mem_ball_self hr⟩

lemma measurable_ball_mass (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (ball x r)) := by
  have hm : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} :=
    isOpen_lt (continuous_snd.dist continuous_fst) continuous_const |>.measurableSet
  exact measurable_measure_prodMk_left hm

lemma measurable_rationalMaximal (ν : Measure ℂ) [SFinite ν] :
    Measurable (rationalMaximal ν) := by
  unfold rationalMaximal
  apply Measurable.iSup
  intro q
  apply Measurable.iSup
  intro _
  have hd : Measurable (fun x : ℂ => volume (ball x (q:ℝ))) := by
    simp only [Complex.volume_ball]
    exact measurable_const
  exact (measurable_ball_mass ν (q:ℝ)).div hd

lemma weak_rationalMaximal {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  apply le_trans (measure_mono ?_) (weak_bound ha)
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  refine ⟨q,hq',?_⟩
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh).le

/-- Truncating an input below half the testing height sharpens weak type by
charging only its large values. This is the interpolation mechanism. -/
lemma weak_split {ν η : Measure ℂ} [IsFiniteMeasure η] {a : ℝ} (ha : 0 < a)
    (hsplit : ∀ x r, 0 < r → ν (ball x r) ≤ η (ball x r)+
      ENNReal.ofReal (a/2)*volume (ball x r)) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal (a/2)) * η univ := by
  apply le_trans (measure_mono ?_) (weak_bound (by linarith : 0 < a/2))
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  have hh' := (ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh
  refine ⟨q,hq',?_⟩
  by_contra h
  have hη : η (ball x (q:ℝ)) ≤ ENNReal.ofReal (a/2)*volume (ball x (q:ℝ)) := (lt_of_not_ge h).le
  have hfull := (hsplit x q hq').trans (add_le_add hη le_rfl)
  have hsum : ENNReal.ofReal (a/2)+ENNReal.ofReal (a/2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ a/2) (by linarith : 0 ≤ a/2)]
    congr 1
    ring
  rw [← add_mul,hsum] at hfull
  exact (not_lt_of_ge hfull) hh'

lemma weak_truncated {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure (volume.withDensity f)] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal (volume.withDensity f) x} ≤
      (25 / ENNReal.ofReal (a/2)) *
        ∫⁻ x, {x | ENNReal.ofReal (a/2) < f x}.indicator f x := by
  let H := {x | ENNReal.ofReal (a/2) < f x}
  let η := volume.withDensity (H.indicator f)
  have hle : η ≤ volume.withDensity f := withDensity_mono (ae_of_all _ (indicator_le_self _ _))
  have : IsFiniteMeasure η := isFiniteMeasure_of_le _ hle
  have hweak := weak_split (ν := volume.withDensity f) (η := η) ha ?_
  · simpa only [η,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ] using hweak
  · intro x r _
    rw [withDensity_apply _ measurableSet_ball,show η = volume.withDensity (H.indicator f) from rfl,
      withDensity_apply _ measurableSet_ball]
    calc
      _ ≤ ∫⁻ y in ball x r, H.indicator f y+ENNReal.ofReal (a/2) := by
        apply lintegral_mono
        intro y
        dsimp only
        by_cases hy : y ∈ H
        · rw [indicator_of_mem hy]
          exact le_add_right le_rfl
        · rw [indicator_of_notMem hy,zero_add]
          exact le_of_not_gt hy
      _ = _ := by
        rw [lintegral_add_left (hf.indicator (measurableSet_lt measurable_const hf))]
        simp only [lintegral_const,Measure.restrict_apply_univ]
        rfl

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace DiskMaximalTools

lemma lintegral_rpow_Ioo {b s : ℝ} (hb : 0 ≤ b) (hs : -1 < s) :
    (∫⁻ t in Ioo 0 b, ENNReal.ofReal (t^s)) = ENNReal.ofReal (b^(s+1)/(s+1)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
  · have hi : IntegrableOn (fun t : ℝ => t^s) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr hs
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.le,
        integral_rpow (Or.inl hs)]
      simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _

lemma truncation_layer_single {b p : ℝ} (hb : 0 ≤ b) (hp : 1 < p) :
    (∫⁻ t in Ioi 0, (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal (b^p) := by
  have heq : (fun t : ℝ => (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      (Iio (2*b)).indicator (fun t => ENNReal.ofReal b * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases ht : t < 2*b <;> simp [ht]
  rw [heq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio (2*b) ∩ Ioi (0:ℝ) = Ioo 0 (2*b) := by ext t; simp [and_comm]
  rw [hi,lintegral_const_mul'' _ (by fun_prop)]
  rw [lintegral_rpow_Ioo (by positivity : 0 ≤ 2*b) (by linarith : -1 < p-2)]
  have hpp : p-2+1 = p-1 := by ring
  rw [hpp]
  have h2 : 0 ≤ (2:ℝ)^(p-1)/(p-1) := div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  rw [← ENNReal.ofReal_mul hb,← ENNReal.ofReal_mul h2]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb]
  have hp0 : 0 < p-1 := by linarith
  have hpow : b*b^(p-1) = b^p := by
    rcases eq_or_lt_of_le hb with rfl | hb
    · simp [Real.zero_rpow hp0.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        b*b^(p-1) = b^(1:ℝ)*b^(p-1) := by rw [Real.rpow_one]
        _ = b^(1+(p-1)) := (Real.rpow_add hb _ _).symm
        _ = b^p := by congr 1; ring
  calc
    b * (2^(p-1)*b^(p-1)/(p-1)) = (2^(p-1)/(p-1))*(b*b^(p-1)) := by ring
    _ = _ := by rw [hpow]

/-- Exact Tonelli computation behind strong maximal interpolation, for every
p > 1. The singularity at testing height zero is actually integrated. -/
theorem truncation_layer_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0,
      (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 ∂μ)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*(∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) := by
  have hm : Measurable (fun z : ℝ × α =>
      (if z.1 < 2*f z.2 then ENNReal.ofReal (f z.2) else 0)*ENNReal.ofReal (z.1^(p-2))) := by
    apply Measurable.mul
    · exact ((hf.comp measurable_snd).ennreal_ofReal).ite
        (measurableSet_lt measurable_fst ((hf.comp measurable_snd).const_mul 2)) measurable_const
    · exact (measurable_fst.pow_const _).ennreal_ofReal
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)) ∂μ := by
      apply lintegral_congr
      intro t
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x, (∫⁻ t in Ioi 0,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal ((f x)^p) ∂μ := by
      apply lintegral_congr
      intro x
      exact truncation_layer_single (hf0 x) hp
    _ = _ := lintegral_const_mul'' _ ((hf.pow_const _).ennreal_ofReal.aemeasurable)

end DiskMaximalTools

namespace DiskMaximalTools

lemma maximal_layer_coefficient {t p : ℝ} (ht : 0 < t) :
    (25 / ENNReal.ofReal (t/2))*ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal 50*ENNReal.ofReal (t^(p-2)) := by
  rw [← show ENNReal.ofReal (25:ℝ) = 25 by norm_num,
    ← ENNReal.ofReal_div_of_pos (by linarith : 0 < t/2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (25:ℝ)/(t/2)),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50)]
  congr 1
  have hpow : t^(p-1) = t*t^(p-2) := by
    calc
      _ = t^(1+(p-2)) := by congr 1; ring
      _ = t^(1:ℝ)*t^(p-2) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- A full strong p estimate from Vitali, truncation and Tonelli. No maximal
inequality is supplied as an assumption. The real representative is controlled
even before a separate almost-everywhere finiteness argument. -/
theorem strong_rationalMaximal {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal ((rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal^p)) ≤
      ENNReal.ofReal (50*p*2^(p-1)/(p-1)) * (∫⁻ x, ENNReal.ofReal ((f x)^p)) := by
  let M := rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x)))
  have hM : Measurable M := measurable_rationalMaximal _
  have htail (t : ℝ) (ht : 0 < t) : volume {x | t < (M x).toReal} ≤
      (25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 := by
    have hsub : {x | t < (M x).toReal} ⊆ {x | ENNReal.ofReal t < M x} := by
      intro x hx
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx |>.trans_le ENNReal.ofReal_toReal_le
    apply le_trans (measure_mono hsub)
    have hweak := weak_truncated hf.ennreal_ofReal ht
    apply hweak.trans_eq
    congr 1
    apply lintegral_congr
    intro x
    have heq : ENNReal.ofReal (t/2) < ENNReal.ofReal (f x) ↔ t < 2*f x := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith : 0 ≤ t/2)]
      constructor <;> intro h <;> linarith
    simp only [Set.indicator,Set.mem_ofPred_eq,heq]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    hM.ennreal_toReal.aemeasurable (by linarith : 0 < p)]
  have hlayer : (∫⁻ t in Ioi 0, volume {x | t < (M x).toReal}*ENNReal.ofReal (t^(p-1))) ≤
      ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
    calc
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal 50 *
          ((∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        calc
          _ ≤ ((25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*
              ENNReal.ofReal (t^(p-1)) := by gcongr; exact htail t ht
          _ = _ := by
            rw [mul_right_comm, maximal_layer_coefficient ht]
            ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal p*(ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)))) := by
      gcongr
    _ = _ := by
      rw [truncation_layer_integral hf hf0 hp]
      have hc : ENNReal.ofReal p*(ENNReal.ofReal 50 * ENNReal.ofReal (2^(p-1)/(p-1))) =
          ENNReal.ofReal (50*p*2^(p-1)/(p-1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50),
          ← ENNReal.ofReal_mul (by linarith : 0 ≤ p)]
        congr 1
        ring
      simpa only [mul_assoc] using congrArg
        (fun c => c*(∫⁻ x, ENNReal.ofReal ((f x)^p))) hc

end DiskMaximalTools

namespace DiskMaximalTools

lemma disk_average_le_rationalMaximal_exact (ν : Measure ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ν (ball x r) / volume (ball x r) ≤ rationalMaximal ν x := by
  let I := {q : ℚ // 0 < q ∧ (q:ℝ) < r}
  have hdir : Directed (· ⊆ ·) (fun q : I => ball x (q:ℚ)) := by
    intro i j
    refine ⟨⟨max i.val j.val,?_,?_⟩,?_,?_⟩
    · exact lt_max_of_lt_left i.property.1
    · exact_mod_cast max_lt i.property.2 j.property.2
    · exact ball_subset_ball (by exact_mod_cast le_max_left i.val j.val)
    · exact ball_subset_ball (by exact_mod_cast le_max_right i.val j.val)
  have heq : (⋃ q : I, ball x (q:ℚ)) = ball x r := by
    ext y
    constructor
    · intro hy
      obtain ⟨q,hq⟩ := mem_iUnion.mp hy
      exact (ball_subset_ball q.property.2.le) hq
    · intro hy
      have hd : dist y x < r := hy
      obtain ⟨q,hq0,hqr⟩ := exists_rat_btwn (show max 0 (dist y x) < r by exact max_lt hr hd)
      have hq : 0 < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq0
      have hqRat : (0:ℚ) < q := by exact_mod_cast hq
      refine mem_iUnion.mpr ⟨⟨q,hqRat,hqr⟩,?_⟩
      exact lt_of_le_of_lt (le_max_right _ _) hq0
  have hv0 : volume (ball x r) ≠ 0 := by
    rw [volume_disk_real _ hr.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [← heq,hdir.measure_iUnion]
  apply iSup_le
  intro q
  have hq0 : 0 < (q.val:ℝ) := by exact_mod_cast q.property.1
  have hqv : volume (ball x (q.val:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq0.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq0)))
  have hav : ν (ball x (q.val:ℝ)) / volume (ball x (q.val:ℝ)) ≤ rationalMaximal ν x :=
    le_iSup_of_le q.val (le_iSup_of_le q.property.1 le_rfl)
  calc
    _ ≤ rationalMaximal ν x * volume (ball x (q.val:ℝ)) :=
      (ENNReal.div_le_iff hqv measure_ball_lt_top.ne).mp hav
    _ ≤ _ := by
      gcongr
      exact subset_iUnion (fun q : I => ball x (q:ℚ)) q

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Kernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
noncomputable section
namespace PlanePotential

lemma dim_complex : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

lemma volume_real_unit_ball : volume.real (ball (0:ℂ) 1) = Real.pi := by
  rw [measureReal_def,Complex.volume_ball]
  simp

lemma integral_radial (f : ℝ → ℝ) :
    (∫ x : ℂ, f ‖x‖) = 2*Real.pi * ∫ r in Ioi (0:ℝ), r*f r := by
  rw [integral_fun_norm_addHaar volume f]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul,volume_real_unit_ball,
    nsmul_eq_mul,Nat.cast_ofNat]
  ring

lemma radial_near_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t * (Iio r).indicator (fun u : ℝ => u^a) t = (Ioo 0 r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : t < r
  · simp only [indicator_of_mem (show t ∈ Iio r from htr),indicator_of_mem (show t ∈ Ioo 0 r from ⟨ht,htr⟩)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Iio r from htr),indicator_of_notMem (show t ∉ Ioo 0 r by simp [htr]),mul_zero]

lemma integrable_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun t : ℝ => t^a)]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioo 0 r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
  apply hi.congr_fun _ measurableSet_Ioo
  intro t ht
  change t^(a+1) = t*t^a
  rw [Real.rpow_add ht.1,Real.rpow_one,mul_comm]

/-- Exact planar singular-kernel integral; the center point is not excluded by
an unproved integrability convention. -/
theorem integral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫ x in ball (0:ℂ) r, ‖x‖^a) = 2*Real.pi * (r^(a+2)/(a+2)) := by
  have heq : (ball (0:ℂ) r).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Iio r).indicator (fun t : ℝ => t^a) ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ < r <;> simp [indicator,hx]
  rw [← integral_indicator measurableSet_ball,heq,integral_radial]
  have hinner : (∫ t in Ioi (0:ℝ), t*(Iio r).indicator (fun u : ℝ => u^a) t) =
      ∫ t in Ioo 0 r, t^(a+1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_near_identity a r ht)]
    rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioi_self)]
  rw [hinner,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith : -1 < a+1))]
  rw [show a+1+1=a+2 by ring,Real.zero_rpow (by linarith : a+2 ≠ 0),sub_zero]

end PlanePotential

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section

open Finset
open scoped RealInnerProductSpace
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace PlanePotential

lemma segment_support {ψ : ℂ → ℝ} {R X : ℝ}
    (hψ : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) {x y : ℂ} (hx : ‖x‖ ≤ X)
    {t : ℝ} (ht : 0 < t) (hn : ψ (x+t⁻¹ • (y-x)) ≠ 0) :
    ‖y-x‖ ≤ t*(R+X) := by
  have heq : y-x = t • ((x+t⁻¹ • (y-x))-x) := by
    simp [ht.ne']
  calc
    ‖y-x‖ = t*‖(x+t⁻¹ • (y-x))-x‖ := by
      conv_lhs => rw [heq]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    _ ≤ t*(‖x+t⁻¹ • (y-x)‖+‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) ht.le
    _ ≤ t*(R+X) := mul_le_mul_of_nonneg_left (add_le_add (hψ _ hn) hx) ht.le

lemma integrable_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    Integrable ((Ioi δ).indicator (fun t : ℝ => B*t^q)) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mpr
  exact (integrableOn_Ioi_rpow_of_lt hq hδ).const_mul B

lemma integral_power_cutoff {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) :
    (∫ t : ℝ, (Ioi δ).indicator (fun t : ℝ => B*t^q) t) = B*(-δ^(q+1)/(q+1)) := by
  rw [integral_indicator measurableSet_Ioi,integral_const_mul,integral_Ioi_rpow_of_lt hq hδ]

/-- A singular segment integral is genuinely integrable because of its geometric
lower cutoff. The bound retains the exact power, rather than a supremum times 1. -/
lemma singular_integral_bound {F : ℝ → ℝ} (hFm : Measurable F)
    {q δ B : ℝ} (hq : q < -1) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → F t = 0)
    (hbound : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ B*t^q) :
    IntegrableOn F (Ioc (0:ℝ) 1) ∧
      |∫ t in Ioc (0:ℝ) 1, F t| ≤ B*(-(δ/2)^(q+1)/(q+1)) := by
  let H := (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q)
  have hH : Integrable H := integrable_power_cutoff hq (by linarith)
  have hH0 (t : ℝ) : 0 ≤ H t := by
    unfold H
    apply indicator_nonneg
    intro t ht
    exact mul_nonneg hB (Real.rpow_nonneg (by change δ/2 < t at ht; linarith) _)
  have hle : ∀ t ∈ Ioc (0:ℝ) 1, |F t| ≤ H t := by
    intro t ht
    by_cases hd : t < δ
    · rw [hzero t ht hd]
      simpa only [abs_zero] using hH0 t
    · have htδ : t ∈ Ioi (δ/2) := by change δ/2 < t; linarith
      change |F t| ≤ (Ioi (δ/2)).indicator (fun t : ℝ => B*t^q) t
      rw [indicator_of_mem htδ]
      exact hbound t ht
  have hFi : IntegrableOn F (Ioc (0:ℝ) 1) := by
    apply hH.integrableOn.mono' hFm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs] using hle t ht
  refine ⟨hFi,?_⟩
  calc
    _ ≤ ∫ t in Ioc (0:ℝ) 1, |F t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioc (0:ℝ) 1, H t := integral_mono_ae hFi.abs hH.integrableOn (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using hle t ht)
    _ ≤ ∫ t, H t := integral_mono_measure Measure.restrict_le_self (ae_of_all _ hH0) hH
    _ = _ := integral_power_cutoff hq (by linarith)

lemma greenScalar_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => greenScalar ψ p.1 p.2) := by
  unfold greenScalar
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  have harg : Measurable (fun p : (ℂ × ℂ) × ℝ => p.1.1+p.2⁻¹ • (p.1.2-p.1.1)) := by measurability
  exact ((hψ.comp harg).mul (measurable_snd.pow_const _)).stronglyMeasurable

lemma green_measurable (ψ : ℂ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun p : ℂ × ℂ => green ψ p.1 p.2) := by
  exact (greenScalar_measurable ψ hψ).neg.smul (measurable_snd.sub measurable_fst)

/-- Quantitative kernel size on every observation ball, with an explicit constant. -/
theorem green_norm_bound {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) (hxy : y ≠ x) :
    ‖green ψ x y‖ ≤ 2*B*(R+X)^2/‖y-x‖ := by
  have hd : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let δ := ‖y-x‖/(R+X)
  have hδ : 0 < δ := div_pos hd hM
  have hFm : Measurable (fun t : ℝ => ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)) := by
    apply Measurable.mul
    · apply hψm.comp
      measurability
    · exact measurable_id.pow_const _
  have hzero : ∀ t ∈ Ioc (0:ℝ) 1, t < δ → ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ) = 0 := by
    intro t ht hlt
    have hψ0 : ψ (x+t⁻¹ • (y-x)) = 0 := by
      by_contra hn
      have hs := segment_support hψs hx ht.1 hn
      have : t*(R+X) < ‖y-x‖ := (lt_div_iff₀ hM).mp hlt
      linarith
    rw [hψ0,zero_mul]
  have hb : ∀ t ∈ Ioc (0:ℝ) 1,
      |ψ (x+t⁻¹ • (y-x))*t^(-3:ℝ)| ≤ B*t^(-3:ℝ) := by
    intro t ht
    rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hψB _) (Real.rpow_nonneg ht.1.le _)
  have h := (singular_integral_bound hFm (by norm_num : (-3:ℝ) < -1) hδ hB hzero hb).2
  change |greenScalar ψ x y| ≤ _ at h
  have hrpow : (δ/2)^((-3:ℝ)+1) = (δ/2)^(-2:ℤ) := by norm_num [Real.rpow_intCast]
  rw [hrpow,zpow_neg,zpow_ofNat] at h
  have hs : |greenScalar ψ x y| ≤ 2*B*(R+X)^2/‖y-x‖^2 := by
    convert h using 1
    dsimp [δ]
    field_simp
    ring
  rw [green,norm_smul,Real.norm_eq_abs,abs_neg]
  calc
    _ ≤ (2*B*(R+X)^2/‖y-x‖^2)*‖y-x‖ := mul_le_mul_of_nonneg_right hs hd.le
    _ = _ := by field_simp

end PlanePotential

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.GreenBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace PlanePotential

lemma integral_affine (F : ℂ → ℝ) (x : ℂ) (t : ℝ) :
    (∫ z : ℂ, F (x+t • (z-x))) = (t^2)⁻¹ * ∫ y : ℂ, F y := by
  calc
    _ = ∫ w : ℂ, F (x+t • w) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fun w : ℂ => F (x+t • w)) (-x)
    _ = |(t^2)⁻¹| * ∫ y, F (x+y) := by
      simpa only [Complex.finrank_real_complex,smul_eq_mul] using
        Measure.integral_comp_smul volume (fun y : ℂ => F (x+y)) t
    _ = _ := by rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),integral_add_left_eq_self]

lemma integrable_affine_iff (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun z : ℂ => F (x+t • (z-x))) ↔ Integrable F := by
  constructor
  · intro h
    have h1 : Integrable (fun z : ℂ => F (x+t • z)) := by
      simpa only [add_sub_cancel_right] using h.comp_add_right x
    have h2 := (integrable_comp_smul_iff volume (fun z : ℂ => F (x+z)) ht).mp h1
    simpa only [add_neg_cancel_left] using h2.comp_add_left (-x)
  · intro h
    simpa only [sub_eq_add_neg] using ((h.comp_add_left x).comp_smul ht).comp_add_right (-x)

lemma integral_affine_reverse (F : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℂ, F y) = t^2 * ∫ z : ℂ, F (x+t • (z-x)) := by
  rw [integral_affine]
  field_simp

lemma segment_ftc {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (x z : ℂ) :
    (∫ t in Ioc (0:ℝ) 1, fderiv ℝ g (x+t • (z-x)) (z-x)) = g z-g x := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => g (x+s • (z-x)))
      (fderiv ℝ g (x+t • (z-x)) (z-x)) t := by
    have hline : HasDerivAt (fun s : ℝ => x+s • (z-x)) (z-x) t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (z-x)).const_add x
    exact ((hg.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt t hline
  have hc : Continuous (fun t : ℝ => fderiv ℝ g (x+t • (z-x)) (z-x)) := by
    exact ((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply continuous_const
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),one_smul,
    add_sub_cancel,zero_smul,add_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable 0 1)

lemma pullback_identity (ψ g : ℂ → ℝ) (x z : ℂ) {t : ℝ} (ht : 0 < t) :
    pullbackForm ψ g x t (x+t • (z-x)) = (t^2)⁻¹*segmentForm ψ g x t z := by
  have ha : x+t⁻¹ • (x+t • (z-x)-x) = z := by simp [ht.ne']
  unfold pullbackForm segmentForm
  rw [ha,add_sub_cancel_left,map_smul,smul_eq_mul]
  have hp : t^(-3:ℝ) = (t^3)⁻¹ := by
    rw [show (-3:ℝ) = ((-3:ℤ):ℝ) by norm_num,Real.rpow_intCast,zpow_neg,zpow_ofNat]
  rw [hp]
  field_simp

lemma segmentForm_continuous {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Continuous (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2) := by
  unfold segmentForm
  exact (hψ.comp continuous_snd).mul
    (((hg.continuous_fderiv (by norm_num)).comp (by fun_prop)).clm_apply (by fun_prop))

lemma segmentForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) (t : ℝ) :
    Integrable (segmentForm ψ g x t) := by
  apply ((segmentForm_continuous hψ hg x).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  exact hψc.mul_right

lemma pullbackForm_measurable {ψ g : ℂ → ℝ} (hψ : Continuous ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) :
    Measurable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2) := by
  unfold pullbackForm
  have ha : Measurable (fun p : ℝ × ℂ => x+p.1⁻¹ • (p.2-x)) := by measurability
  exact ((hψ.measurable.comp ha).mul (measurable_fst.pow_const _)).mul
    ((((hg.continuous_fderiv (by norm_num)).comp continuous_snd).clm_apply (by fun_prop)).measurable)

lemma pullbackForm_integrable_column {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    Integrable (pullbackForm ψ g x t) := by
  apply (integrable_affine_iff _ x ht.ne').mp
  simpa only [pullback_identity ψ g x _ ht] using
    (segmentForm_integrable_column hψ hψc hg x t).const_mul ((t^2)⁻¹)

lemma pullback_column_integral (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, pullbackForm ψ g x t y) = ∫ z, segmentForm ψ g x t z := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht]
  rw [integral_const_mul]
  field_simp

lemma pullback_column_norm (ψ g : ℂ → ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    (∫ y, ‖pullbackForm ψ g x t y‖) = ∫ z, ‖segmentForm ψ g x t z‖ := by
  rw [integral_affine_reverse _ x ht.ne']
  simp_rw [pullback_identity ψ g x _ ht,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  rw [integral_const_mul]
  field_simp

lemma segmentForm_bound {ψ g : ℂ → ℝ} {D : ℝ} (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D)
    (x : ℂ) (t : ℝ) (z : ℂ) :
    ‖segmentForm ψ g x t z‖ ≤ |ψ z| *D*‖z-x‖ := by
  rw [segmentForm,norm_mul,Real.norm_eq_abs]
  calc
    _ ≤ |ψ z| *(‖fderiv ℝ g (x+t • (z-x))‖*‖z-x‖) :=
      mul_le_mul_of_nonneg_left ((fderiv ℝ g _).le_opNorm _) (abs_nonneg _)
    _ ≤ |ψ z| *(D*‖z-x‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

lemma segment_weight_integrable {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (x : ℂ) (D : ℝ) :
    Integrable (fun z : ℂ => |ψ z| *D*‖z-x‖) := by
  apply (show Continuous (fun z : ℂ => |ψ z| *D*‖z-x‖) by fun_prop).integrable_of_hasCompactSupport
  exact (hψc.norm.mul_right).mul_right

/-- Absolute integrability justifies the double integral even at t approaching zero. -/
theorem pullbackForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => pullbackForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (pullbackForm_measurable hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pullbackForm_integrable_column hψ hψc hg x ht.1
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| *D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [pullback_column_norm ψ g x ht.1,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma segmentForm_integrable {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) :
    Integrable (fun p : ℝ × ℂ => segmentForm ψ g x p.1 p.2)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
  have hm := (segmentForm_continuous hψ hg x).stronglyMeasurable
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ (fun t => segmentForm_integrable_column hψ hψc hg x t)
  · have hweight := segment_weight_integrable hψ hψc x D
    let C := ∫ z : ℂ, |ψ z| * D*‖z-x‖
    apply (integrable_const C).mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_mono (segmentForm_integrable_column hψ hψc hg x t).norm hweight
      (segmentForm_bound hD x t)

lemma green_pullback (ψ g : ℂ → ℝ) (x y : ℂ) :
    fderiv ℝ g y (green ψ x y) = -∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y := by
  simp only [green,map_smul,smul_eq_mul,greenScalar,pullbackForm,integral_mul_const,neg_mul]

/-- The true segment-kernel representation, with Fubini justified absolutely. -/
theorem green_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, fderiv ℝ g y (green ψ x y)) = g x-∫ z, ψ z*g z := by
  have hseg := segmentForm_integrable hψ hψc hg hD x
  have hpull := pullbackForm_integrable hψ hψc hg hD x
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hψgi : Integrable (fun z => ψ z*g z) :=
    (hψ.mul hg.continuous).integrable_of_hasCompactSupport hψc.mul_right
  calc
    _ = -(∫ y, ∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y) := by
      simp_rw [green_pullback]; rw [integral_neg]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ y, pullbackForm ψ g x t y) := by
      rw [← integral_integral_swap hpull]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ z, segmentForm ψ g x t z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pullback_column_integral ψ g x ht.1
    _ = -(∫ z, ∫ t in Ioc (0:ℝ) 1, segmentForm ψ g x t z) := by
      rw [integral_integral_swap hseg]
    _ = -(∫ z, ψ z*(g z-g x)) := by
      simp_rw [segmentForm,integral_const_mul,segment_ftc hg]
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hψgi (hψi.mul_const _),integral_mul_const,hψ1]
      ring

end PlanePotential

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace PlanePotential
lemma lintegral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫⁻ x in ball (0:ℂ) r, ENNReal.ofReal (‖x‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_near ha hr)
    (ae_of_all _ (fun x => Real.rpow_nonneg (norm_nonneg x) a)),integral_norm_rpow_near ha hr]

lemma lintegral_translated_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) (y : ℂ) :
    (∫⁻ x in ball y r, ENNReal.ofReal (‖x-y‖^a)) =
      ENNReal.ofReal (2*Real.pi*(r^(a+2)/(a+2))) := by
  rw [← lintegral_norm_rpow_near ha hr,← lintegral_indicator measurableSet_ball,
    ← lintegral_indicator measurableSet_ball]
  have heq : (ball y r).indicator (fun x => ENNReal.ofReal (‖x-y‖^a)) =
      fun x => (ball (0:ℂ) r).indicator (fun w => ENNReal.ofReal (‖w‖^a)) (x-y) := by
    funext x
    simp only [indicator,mem_ball,dist_eq_norm,sub_zero]
  rw [heq]
  exact lintegral_add_right_eq_self (fun x : ℂ => (ball 0 r).indicator
    (fun w => ENNReal.ofReal (‖w‖^a)) x) (-y)

lemma norm_power_bound {F : ℂ → ℂ} {C q : ℝ} (hC : 0 ≤ C) (x y : ℂ)
    (hF : ‖F x‖ ≤ C*‖x-y‖^q) :
    (ENNReal.ofReal ‖F x‖)^(3/2:ℝ) ≤
      ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(q*(3/2:ℝ))) := by
  calc
    _ = ENNReal.ofReal (‖F x‖^(3/2:ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)
    _ ≤ ENNReal.ofReal ((C*‖x-y‖^q)^(3/2:ℝ)) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hF (by norm_num))
    _ = _ := by
      rw [Real.mul_rpow hC (Real.rpow_nonneg (norm_nonneg _) _),← Real.rpow_mul (norm_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]

lemma kernel_near_three_halves {F : ℂ → ℂ} {E : Set ℂ} {C r : ℝ} (hC : 0 ≤ C)
    (hr : 0 < r) (y : ℂ) (hE : E ⊆ ball y r)
    (hF : ∀ x ∈ E, ‖F x‖ ≤ C*‖x-y‖^(-1:ℝ)) :
    (∫⁻ x in E, (ENNReal.ofReal ‖F x‖)^(3/2:ℝ)) ≤
      ENNReal.ofReal (C^(3/2:ℝ)*(4*Real.pi*r^(1/2:ℝ))) := by
  calc
    _ ≤ ∫⁻ x in E, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) := by
      apply setLIntegral_mono (by fun_prop)
      intro x hx
      convert norm_power_bound hC x y (hF x hx) using 1
      norm_num
    _ ≤ ∫⁻ x in ball y r, ENNReal.ofReal (C^(3/2:ℝ))*ENNReal.ofReal (‖x-y‖^(-3/2:ℝ)) :=
      lintegral_mono_set hE
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop),lintegral_translated_near (by norm_num : (-2:ℝ) < -3/2) hr y,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
      congr 1
      norm_num
      exact Or.inl (by ring)

end PlanePotential

open scoped RealInnerProductSpace
namespace PlanePotential

lemma green_diagonal (ψ : ℂ → ℝ) (x : ℂ) : green ψ x x = 0 := by
  simp [green]

lemma green_size_all {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) {x y : ℂ} (hx : ‖x‖ ≤ X) :
    ‖green ψ x y‖ ≤ (2*B*(R+X)^2)*‖x-y‖^(-1:ℝ) := by
  by_cases hxy : y = x
  · subst y
    simp [green_diagonal]
  · simpa only [Real.rpow_neg_one,div_eq_mul_inv,norm_sub_rev] using
      green_norm_bound hψm hψs hψB hM hB hx hxy

end PlanePotential

namespace PlanePotential

theorem kernel_column_lp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {K : α × β → ℝ≥0∞} (hK : Measurable K) {C : ℝ≥0∞}
    (hC : ∀ᵐ y ∂ν, (∫⁻ x, (K (x,y))^(3/2:ℝ) ∂μ) ≤ C) :
    (∫⁻ x, (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ∂μ) ≤ C*(ν univ)^(3/2:ℝ) := by
  have hpq : Real.HolderConjugate (3/2) 3 := by rw [Real.holderConjugate_iff]; norm_num
  have hpoint (x : α) : (∫⁻ y, K (x,y) ∂ν)^(3/2:ℝ) ≤
      (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq (f := fun y => K (x,y)) (g := fun _ => 1)
      ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)
      (aemeasurable_const (b := (1:ℝ≥0∞)))
    simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 3/2)
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 3/2),← ENNReal.rpow_mul,
      show (1/(3/2:ℝ))*(3/2)=1 by norm_num,
      show (1/(3:ℝ))*(3/2)=1/2 by norm_num,ENNReal.rpow_one,one_mul] using h'
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, K (x,y)^(3/2:ℝ) ∂ν)*(ν univ)^(1/2:ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ y, ∫⁻ x, K (x,y)^(3/2:ℝ) ∂μ ∂ν)*(ν univ)^(1/2:ℝ) := by
      rw [lintegral_mul_const _ (hK.pow_const _).lintegral_prod_right,
        lintegral_lintegral_swap (hK.pow_const _).aemeasurable]
    _ ≤ (C*ν univ)*(ν univ)^(1/2:ℝ) :=
      mul_le_mul_left ((lintegral_mono_ae hC).trans_eq (lintegral_const _)) _
    _ = _ := by
      rw [mul_assoc]
      congr 1
      calc
        _ = (ν univ)^(1:ℝ)*(ν univ)^(1/2:ℝ) := by rw [ENNReal.rpow_one]
        _ = (ν univ)^((1:ℝ)+1/2) :=
          (ENNReal.rpow_add_of_nonneg 1 (1/2) (by norm_num) (by norm_num)).symm
        _ = _ := by norm_num

/-- No pointwise integrability assertion for the singular kernel is needed
in this domination: the Bochner integral is bounded by the nonnegative integral. -/
lemma potential_domination {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    ENNReal.ofReal |∫ y, ⟪L y,b y⟫| ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  calc
    _ = ‖∫ y, ⟪L y,b y⟫‖ₑ := by rw [← ofReal_norm,Real.norm_eq_abs]
    _ ≤ ∫⁻ y, ‖⟪L y,b y⟫‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
      apply lintegral_mono
      intro y
      dsimp only [Pi.mul_apply]
      rw [← ofReal_norm]
      change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

end PlanePotential

open scoped RealInnerProductSpace
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Marks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

open scoped ContDiff
namespace PlanePotential

lemma green_root_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y) {y : ℂ} (hy : ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 2*(X+Y)) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have hn := norm_sub_le x y
    change ‖x‖ ≤ X at hx
    linarith
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx

lemma green_root_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := green_measurable ψ hψm
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ)))) (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_root_column hψm hψs hψB hM hB hXY
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

end PlanePotential

namespace PlanePotential
lemma eLpNorm_three_halves_bound (μ : Measure ℂ) {F : ℂ → ℝ} {K m : ℝ≥0∞}
    (h : (∫⁻ x, (ENNReal.ofReal |F x|)^(3/2:ℝ) ∂μ) ≤ K*m^(3/2:ℝ)) :
    eLpNorm' F (3/2) μ ≤ K^(2/3:ℝ)*m := by
  rw [eLpNorm'_eq_lintegral_enorm]
  norm_num only [one_div_div]
  have hpow := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul] at hpow
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,ENNReal.rpow_one] at hpow
  simpa only [← ofReal_norm,Real.norm_eq_abs] using hpow

/-- A genuine fixed smooth probability cutoff. Its finite size and Lipschitz
constants depend on no input, no dyadic level and no number of scales. -/
theorem exists_kernel_cutoff : ∃ (ψ : ℂ → ℝ) (B L : ℝ),
    0 ≤ B ∧ 0 ≤ L ∧ ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x) = 1 ∧ (∀ x, ψ x ≠ 0 → ‖x‖ ≤ 1) ∧
    (∀ x, |ψ x| ≤ B) ∧ (∀ x y, |ψ x-ψ y| ≤ L*‖x-y‖) := by
  let φ : ContDiffBump (0:ℂ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let ψ := φ.normed volume
  have hc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hd : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hd.continuous
  obtain ⟨L,hL⟩ := hd.lipschitzWith_of_hasCompactSupport hc (by simp)
  refine ⟨ψ,B,L,le_trans (norm_nonneg (ψ 0)) (hB 0),L.coe_nonneg,hd,hc,
    φ.integral_normed,?_,?_,?_⟩
  · intro x hx
    have hs : x ∈ Function.support ψ := hx
    rw [φ.support_normed_eq] at hs
    exact (show ‖x‖ < 1 by simpa only [mem_ball,dist_zero_right] using hs).le
  · intro x
    simpa only [Real.norm_eq_abs] using hB x
  · intro x y
    simpa only [Real.norm_eq_abs] using hL.norm_sub_le x y

end PlanePotential

open Finset
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

namespace PlanePotential

/-- The global segment kernel vanishes off the region on which the actual
finite density decomposition is valid. -/
lemma green_eq_zero_of_outside {ψ : ℂ → ℝ} {R X : ℝ}
    (hs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X) {x y : ℂ}
    (hx : ‖x‖ ≤ X) (hy : X < ‖y‖) : green ψ x y = 0 := by
  have hz (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : ψ (x+t⁻¹ • (y-x)) = 0 := by
    by_contra hh
    have hw := hs _ hh
    have heq : y = (1-t) • x+t • (x+t⁻¹ • (y-x)) := by
      rw [smul_add,smul_smul,mul_inv_cancel₀ ht.1.ne',one_smul]
      module
    have hn := norm_add_le ((1-t) • x) (t • (x+t⁻¹ • (y-x)))
    rw [← heq,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2),abs_of_pos ht.1] at hn
    have hle := add_le_add (mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left (hw.trans hRX) ht.1.le)
    nlinarith
  have hi : greenScalar ψ x y = 0 := by
    unfold greenScalar
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    simp only [hz t ht,zero_mul]
  simp only [green,hi,neg_zero,zero_smul]

lemma green_gradient_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, ⟪green ψ x y,gradient g y⟫) = g x-∫ z, ψ z*g z := by
  simpa only [inner_gradient_right,RCLike.conj_to_real] using
    green_representation hψ hψc hg hD hψ1 x

end PlanePotential

namespace RadiusEnvelope
variable {E : Type*}

lemma attains {u : ℝ → E → ℝ} {a b : ℝ} (hab : a ≤ b) (x : E)
    (hc : ContinuousOn (fun r => u r x) (Icc a b)) :
    ∃ r ∈ Icc a b, envelope u a b x = u r x ∧ ∀ t ∈ Icc a b, u t x ≤ u r x := by
  obtain ⟨r,hr,hm⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hc
  refine ⟨r,hr,?_,hm⟩
  apply le_antisymm
  · apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
    rintro _ ⟨t,ht,rfl⟩
    exact hm ht
  · apply le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    exact mem_image_of_mem _ hr

lemma le_envelope {u : ℝ → E → ℝ} {a b r : ℝ} (hr : r ∈ Icc a b) (x : E)
    (hc : ContinuousOn (fun r => u r x) (Icc a b)) : u r x ≤ envelope u a b x := by
  obtain ⟨t,ht,he,hm⟩ := attains (hr.1.trans hr.2) x hc
  rw [he]
  exact hm r hr

lemma lipschitz [NormedAddCommGroup E] {u : ℝ → E → ℝ} {a b : ℝ} {L : ℝ≥0} (hab : a ≤ b)
    (hc : ∀ x, ContinuousOn (fun r => u r x) (Icc a b))
    (hL : ∀ r ∈ Icc a b, LipschitzWith L (u r)) :
    LipschitzWith L (envelope u a b) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  obtain ⟨r,hr,her,hmr⟩ := attains hab x (hc x)
  obtain ⟨t,ht,het,hmt⟩ := attains hab y (hc y)
  rw [Real.dist_eq,abs_le]
  constructor
  · have h := (hL t ht).dist_le_mul x y
    rw [Real.dist_eq] at h
    rw [het]
    have hx := le_envelope ht x (hc x)
    have ha := (abs_le.mp h).1
    linarith
  · have h := (hL r hr).dist_le_mul x y
    rw [Real.dist_eq] at h
    rw [her]
    have hy := le_envelope hr y (hc y)
    have ha := (abs_le.mp h).2
    linarith

lemma zero_of_all_zero {u : ℝ → E → ℝ} {a b : ℝ} (hab : a ≤ b) {x : E}
    (hc : ContinuousOn (fun r => u r x) (Icc a b))
    (hz : ∀ r ∈ Icc a b, u r x = 0) : envelope u a b x = 0 := by
  obtain ⟨r,hr,he,_⟩ := attains hab x hc
  exact he.trans (hz r hr)

/-- Differentiable touching holds for every attaining radius; no derivative of
an argmax selector is taken. -/
theorem fderiv_touching [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ → E → ℝ} {a b r : ℝ} {x : E}
    (hr : r ∈ Icc a b) (hc : ∀ y, ContinuousOn (fun t => u t y) (Icc a b))
    (he : envelope u a b x = u r x)
    (hd : DifferentiableAt ℝ (envelope u a b) x) (hu : DifferentiableAt ℝ (u r) x) :
    fderiv ℝ (envelope u a b) x = fderiv ℝ (u r) x := by
  have hm : IsLocalMin (fun y => envelope u a b y-u r y) x := by
    apply IsMinOn.isLocalMin (s := univ) _ univ_mem
    intro y _
    change envelope u a b x-u r x ≤ envelope u a b y-u r y
    rw [he,sub_self]
    exact sub_nonneg.mpr (le_envelope hr y (hc y))
  have hz := hm.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub hu.hasFDerivAt)
  exact sub_eq_zero.mp hz

end RadiusEnvelope

namespace DiskMoments

lemma signedAverage_radius_continuousOn {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t => signedAverage g x t) (Icc a b) := by
  intro t ht
  exact (hasDerivAt_signedAverage hg x (ha.trans_le ht.1)).continuousAt.continuousWithinAt

lemma hasFDerivAt_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    HasFDerivAt (fun x => signedAverage g x t)
      ((1/Real.pi) • ∫ z in Metric.ball 0 1, fderiv ℝ g (x+t • z)) x := by
  let F : ℂ → ℂ → ℝ := fun x z => g (x+t • z)
  have hFi : IntegrableOn (F x) (Metric.ball 0 1) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall 0 1)
      (hg.continuous.comp (by fun_prop)).continuousOn).mono_set Metric.ball_subset_closedBall
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Metric.ball (0:ℂ) 1)) (F := F)
    (F' := fun x z => fderiv ℝ g (x+t • z)) (bound := fun _ => D)
    (s := univ) (x₀ := x) univ_mem
    (Eventually.of_forall (fun x => (hg.continuous.comp (by fun_prop)).aestronglyMeasurable))
    hFi ((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ (fun z x _ => hD (x+t • z))) (integrableOn_const (by finiteness))
    (ae_of_all _ (fun z x _ => by
      simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq,F] using
        (hg.differentiable one_ne_zero (x+t • z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const (t • z))))
  convert! hd.const_mul (1/Real.pi) using 1
  · funext y
    simpa only [F,div_eq_mul_inv,one_div,mul_comm,mul_one] using signedAverage_fixedDomain g y ht

end DiskMoments

namespace DiskMoments

lemma signedAverage_eq_zero_of_outside {g : ℂ → ℝ} {R : ℝ}
    (hs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R) {x : ℂ} {t : ℝ} (hx : R+t ≤ ‖x‖) :
    signedAverage g x t = 0 := by
  unfold signedAverage
  have hz : (∫ y in Metric.ball x t, g y) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    by_contra hny
    have hn := hs y hny
    have hd : ‖x-y‖ < t := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hy
    have hh : ‖x‖ ≤ ‖x-y‖+‖y‖ := by simpa only [sub_add_cancel] using norm_add_le (x-y) y
    linarith
  rw [hz,zero_div]

/-- Every radius in the run is retained, but a common compact spatial support
still exists. -/
theorem run_envelope_hasCompactSupport {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    HasCompactSupport (RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b) := by
  obtain ⟨R,hR⟩ := hgc.isBounded.subset_closedBall (0:ℂ)
  have hs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R := by
    intro y hy
    simpa only [Metric.mem_closedBall,dist_zero_right] using hR (subset_tsupport g hy)
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) (R+b)) isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  by_contra hn
  have hz : RadiusEnvelope.envelope (fun r x => signedAverage g x r) a b x = 0 := by
    apply RadiusEnvelope.zero_of_all_zero hab (signedAverage_radius_continuousOn hg x ha)
    intro r hr
    exact signedAverage_eq_zero_of_outside hs (by linarith [hr.2])
  exact hx hz

end DiskMoments

namespace DyadicHats

lemma boxNorm_le_norm (x : ℂ) : boxNorm x ≤ ‖x‖ :=
  max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

end DyadicHats

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
noncomputable section

namespace LipschitzWith
open scoped _root_.LipschitzWith
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ] {f g : E → ℝ} {L K : ℝ≥0}

/-- Genuine integration by parts for Lipschitz weights and compact Lipschitz
potentials. Differentiability is required only almost everywhere, and follows
from Rademacher rather than being a new premise. -/
theorem integral_fderiv_mul_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, fderiv ℝ f x v * g x ∂μ) = -∫ x, fderiv ℝ g x v * f x ∂μ := by
  have h1 : (fun x => fderiv ℝ f x v*g x) =ᵐ[μ] fun x => lineDeriv ℝ f x v*g x := by
    filter_upwards [hf.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  have h2 : (fun x => lineDeriv ℝ g x (-v)*f x) =ᵐ[μ] fun x => -(fderiv ℝ g x v*f x) := by
    filter_upwards [hg.ae_differentiableAt (μ := μ)] with x hx
    rw [hx.lineDeriv_eq_fderiv,map_neg,neg_mul]
  rw [integral_congr_ae h1,hf.integral_lineDeriv_mul_eq hg hgc v,integral_congr_ae h2,integral_neg]

/-- The total gradient version obtained from Riesz and measurable fderiv is
locally integrable, including on the nondifferentiability set. -/
theorem locallyIntegrable_gradient (hf : LipschitzWith L f) :
    LocallyIntegrable (gradient f) μ := by
  have hm : AEStronglyMeasurable (gradient f) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)).aestronglyMeasurable
  have hb : ∀ x, ‖gradient f x‖ ≤ (L:ℝ) := by
    intro x
    simpa only [gradient,(InnerProductSpace.toDual ℝ E).symm.norm_map] using
      (norm_fderiv_le_of_lipschitz ℝ hf : ‖fderiv ℝ f x‖ ≤ (L:ℝ))
  exact (memLp_top_of_bound hm (L:ℝ) (ae_of_all _ hb)).locallyIntegrable le_top

theorem integrable_gradient (hf : LipschitzWith L f) (hc : HasCompactSupport f) :
    Integrable (gradient f) μ := by
  have hs : HasCompactSupport (gradient f) :=
    (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ E).symm)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport (gradient f))).mp
    ((_root_.OAI.LipschitzWith.locallyIntegrable_gradient (μ := μ) hf).integrableOn_isCompact hs)

theorem integral_mul_fderiv_eq_neg (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hgc : HasCompactSupport g) (v : E) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) = -∫ x, inner ℝ (gradient f x) v * g x ∂μ := by
  simp only [gradient,InnerProductSpace.toDual_symm_apply]
  have h := _root_.OAI.LipschitzWith.integral_fderiv_mul_eq_neg (μ := μ) hf hg hgc v
  rw [show (fun x => f x * fderiv ℝ g x v) = (fun x => fderiv ℝ g x v * f x) by
    funext x; exact mul_comm _ _]
  linarith

end LipschitzWith

open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

end
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.DirectionEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace DirectionNeighbors
open DyadicHats Finset

lemma mem_window_iff {r : ℝ} (hr : 0 < r) (d : ℕ) (q z : ℤ × ℤ) :
    z ∈ window d q ↔ boxNorm (point r z-point r q) ≤ (d:ℝ)*r := by
  have hh (a b : ℤ) : |r*a-r*b| ≤ (d:ℝ)*r ↔ b-(d:ℤ) ≤ a ∧ a ≤ b+d := by
    rw [← mul_sub,abs_mul,abs_of_pos hr,mul_comm (d:ℝ) r,mul_le_mul_iff_right₀ hr]
    have hc : |(a:ℝ)-(b:ℝ)| ≤ (d:ℝ) ↔ |a-b| ≤ (d:ℤ) := by
      exact_mod_cast Iff.rfl
    rw [hc,abs_le]
    omega
  change (_ ∈ ((Finset.Icc _ _) ×ˢ (Finset.Icc _ _))) ↔ max _ _ ≤ _
  rw [Finset.mem_product,Finset.mem_Icc,Finset.mem_Icc,max_le_iff]
  exact (hh _ _).symm.and (hh _ _).symm

end DirectionNeighbors

/-! Actual fixed palette and literal cone coordinates. -/

open MeasureTheory Set
open scoped RealInnerProductSpace
end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace DirectionNeighbors
open DyadicHats

lemma card_window (d : ℕ) (q : ℤ × ℤ) : (window d q).card = (2*d+1)^2 := by
  change ((Finset.Icc (q.1-(d:ℤ)) (q.1+d)) ×ˢ
    (Finset.Icc (q.2-(d:ℤ)) (q.2+d))).card = _
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have hq (z : ℤ) : (z+(d:ℤ)+1-(z-d)).toNat = 2*d+1 := by omega
  rw [hq,hq,pow_two]

end DirectionNeighbors

namespace AffineDensities
lemma gradient_affine {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) (r : ℝ) (X : ℂ) :
    gradient (fun Y => g (p+r • Y)) X = rescale p r (gradient g) X := by
  have hA : HasFDerivAt (fun Y : ℂ => p+r • Y) (r • ContinuousLinearMap.id ℝ ℂ) X :=
    ((hasFDerivAt_id X).const_smul r).const_add p
  have hc := (hg (p+r • X)).hasFDerivAt.comp X hA
  change HasFDerivAt (fun Y => g (p+r • Y)) _ X at hc
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient,rescale,map_smul]
  rw [hc.fderiv]
  ext z
  simp
end AffineDensities

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Potentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace PlanePotential
open LocalCancellation

lemma green_restrict_density {ψ : ℂ → ℝ} {R X : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hRX : R ≤ X)
    (β : ℂ → ℂ) {x : ℂ} (hx : ‖x‖ ≤ X) (y : ℂ) :
    ⟪green ψ x y, ({y : ℂ | ‖y‖ ≤ X}.indicator β) y⟫ = ⟪green ψ x y,β y⟫ := by
  by_cases hy : ‖y‖ ≤ X
  · simp [hy]
  · rw [green_eq_zero_of_outside hψs hRX hx (lt_of_not_ge hy)]
    simp

end PlanePotential

namespace DiskMoments
open DiskMaximalTools

lemma signedAverage_sub_const {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    signedAverage (fun y => g y-c) x t = signedAverage g x t-c := by
  have hi : IntegrableOn g (Metric.ball x t) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x t)).mono_set Metric.ball_subset_closedBall
  have hc : IntegrableOn (fun _ : ℂ => c) (Metric.ball x t) := integrableOn_const measure_ball_lt_top.ne
  unfold signedAverage
  rw [integral_sub hi hc,integral_const]
  have hv : (volume (Metric.ball x t)).toReal = Real.pi*t^2 := by
    rw [volume_disk_real x ht.le,ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real,Measure.restrict_apply_univ,hv,smul_eq_mul]
  field_simp

end DiskMoments

namespace PhysicalCells
open MeasureTheory Set

lemma unitCell_measurable : MeasurableSet unitCell :=
  (Complex.measurable_re measurableSet_Ico).inter (Complex.measurable_im measurableSet_Ico)
lemma toUnit_continuous (p : ℂ) (r : ℝ) : Continuous (toUnit p r) := by unfold toUnit; fun_prop
lemma cell_measurable (p : ℂ) (r : ℝ) : MeasurableSet (cell p r) :=
  (toUnit_continuous p r).measurable unitCell_measurable
lemma norm_unitCell {X : ℂ} (hX : X ∈ unitCell) : ‖X‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im X
  rw [abs_of_nonneg hX.1.1,abs_of_nonneg hX.2.1] at h
  linarith [hX.1.2,hX.2.2]
lemma affine_toUnit (p : ℂ) {r : ℝ} (hr : r ≠ 0) (y : ℂ) : p+r • toUnit p r y = y := by
  simp [toUnit,hr]

end PhysicalCells

namespace DiskMoments

lemma gradient_signedAverage {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (x : ℂ) {t : ℝ} (ht : 0 < t) :
    gradient (fun y => signedAverage g y t) x =
      (Real.pi*t^2)⁻¹ • ∫ y in Metric.ball x t, gradient g y := by
  have hi : IntegrableOn (fun z : ℂ => fderiv ℝ g (x+t • z)) (Metric.ball 0 1) :=
    (((hg.continuous_fderiv one_ne_zero).comp (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0:ℂ) 1)).mono_set Metric.ball_subset_closedBall
  rw [gradient,(hasFDerivAt_signedAverage hg hD x ht).fderiv,map_smul]
  have he := (InnerProductSpace.toDual ℝ ℂ).symm.toContinuousLinearMap.integral_comp_comm hi
  change (∫ z in Metric.ball (0:ℂ) 1, (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ g (x+t • z))) =
    (InnerProductSpace.toDual ℝ ℂ).symm (∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ g (x+t • z)) at he
  rw [← he]
  change (1/Real.pi) • (∫ z in Metric.ball (0:ℂ) 1, gradient g (x+t • z)) = _
  rw [integral_scale_ball (fun z => gradient g (x+z)) ht,integral_translate_ball,smul_smul]
  congr 1
  ring

end DiskMoments

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.SpatialBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace PhysicalCells
open DyadicHats DirectionNeighbors CommonPrices Finset

lemma toUnit_point_re (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).re = y.re/r-p.1 := by
  simp only [toUnit,Complex.smul_re,Complex.sub_re,point,smul_eq_mul]
  field_simp

lemma toUnit_point_im (r : ℝ) (hr : r ≠ 0) (p : ℤ × ℤ) (y : ℂ) :
    (toUnit (point r p) r y).im = y.im/r-p.2 := by
  simp only [toUnit,Complex.smul_im,Complex.sub_im,point,smul_eq_mul]
  field_simp

lemma mem_index_cell {r : ℝ} (hr : 0 < r) (y : ℂ) :
    y ∈ cell (point r (gridIndex r y)) r := by
  change (toUnit _ r y).re ∈ Set.Ico (0:ℝ) 1 ∧ (toUnit _ r y).im ∈ Set.Ico (0:ℝ) 1
  rw [toUnit_point_re r hr.ne',toUnit_point_im r hr.ne']
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.re/r)]
  · exact sub_nonneg.mpr (Int.floor_le _)
  · dsimp only [gridIndex]; linarith [Int.lt_floor_add_one (y.im/r)]

lemma cells_cover {r : ℝ} (hr : 0 < r) : (⋃ p : ℤ × ℤ, cell (point r p) r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact Set.mem_iUnion.mpr ⟨gridIndex r y,mem_index_cell hr y⟩

lemma lintegral_le_cells {r : ℝ} (hr : 0 < r) (F : ℂ → ℝ≥0∞) :
    (∫⁻ y, F y) ≤ ∑' p : ℤ × ℤ, ∫⁻ y in cell (point r p) r, F y := by
  have h := lintegral_iUnion_le (μ := (volume : Measure ℂ)) (fun p : ℤ × ℤ => cell (point r p) r) F
  simpa only [cells_cover hr,Measure.restrict_univ] using h

lemma tsum_ofReal_le {ι : Type*} (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (A : ℝ)
    (hbudget : ∀ s : Finset ι, ∑ i ∈ s, B i ≤ A) :
    (∑' i, ENNReal.ofReal (B i)) ≤ ENNReal.ofReal A := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hB i)]
  exact ENNReal.ofReal_le_ofReal (hbudget s)

/-- Global integration over the actual full lattice. The budget is tested on
arbitrary finite sets, so neither support cutoffs nor omitted cells enter. -/
lemma integral_cell_budget {r : ℝ} (hr : 0 < r) (F : ℂ → ℝ≥0∞)
    (B : (ℤ × ℤ) → ℝ) (hB : ∀ p, 0 ≤ B p) (A : ℝ)
    (hcell : ∀ p, (∫⁻ y in cell (point r p) r, F y) ≤ ENNReal.ofReal (B p))
    (hbudget : ∀ s : Finset (ℤ × ℤ), ∑ p ∈ s, B p ≤ A) :
    (∫⁻ y, F y) ≤ ENNReal.ofReal A :=
  (lintegral_le_cells hr F).trans ((ENNReal.tsum_le_tsum hcell).trans (tsum_ofReal_le B hB A hbudget))

end PhysicalCells

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma HasGradient.congr_ae {f f' : E → ℝ} {g g' : E → E}
    (h : HasGradient (μ := μ) f g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    HasGradient (μ := μ) f' g' := by
  intro φ hφ hc v
  calc
    _ = (∫ x, f x * fderiv ℝ φ x v ∂μ) := integral_congr_ae (hf.symm.mono (fun _ hx => by simp only [hx]))
    _ = _ := h φ hφ hc v
    _ = _ := by congr 1; exact integral_congr_ae (hg.mono (fun _ hx => by simp only [hx]))

lemma contDiff_hasGradient {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    HasGradient (μ := μ) f (gradient f) := by
  intro φ hφ hc v
  simp_rw [inner_gradient_left]
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hf.continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro x _; exact hf.differentiable one_ne_zero x
  · intro x _; exact hφ.differentiable (by simp) x

omit [μ.IsAddHaarMeasure] in
lemma HasGradient.mul_contDiff {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    HasGradient (μ := μ) (fun x => χ x*f x)
      (fun x => χ x • g x + f x • gradient χ x) := by
  intro φ hφ hφc v
  have hdχ : Continuous (fun x => fderiv ℝ χ x v) := (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun x => f x*(χ x*fderiv ℝ φ x v)) μ :=
    hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hχ.continuous.mul hdφ) hc.mul_right
  have h2 : Integrable (fun x => f x*(φ x*fderiv ℝ χ x v)) μ :=
    hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hφ.continuous.mul hdχ) hφc.mul_right
  have h3 : Integrable (fun x => ⟪g x,v⟫*(χ x*φ x)) μ :=
    (hg.inner_const (𝕜 := ℝ) v).locallyIntegrable.integrable_smul_right_of_hasCompactSupport (hχ.continuous.mul hφ.continuous) hc.mul_right
  have h := hw (χ*φ) (hχ.mul hφ) (hc.mul_right) v
  have he (x) : fderiv ℝ (χ*φ) x v = χ x*fderiv ℝ φ x v+φ x*fderiv ℝ χ x v := by
    rw [fderiv_mul (hχ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    rfl
  simp_rw [he,mul_add] at h
  rw [integral_add h1 h2] at h
  have he2 (x) : ⟪χ x • g x + f x • gradient χ x,v⟫ * φ x =
      ⟪g x,v⟫*(χ x*φ x)+f x*(φ x*fderiv ℝ χ x v) := by
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left,inner_gradient_left]
    ring
  simp_rw [he2]
  rw [integral_add h3 h2]
  have hi : (∫ x, χ x*f x*fderiv ℝ φ x v ∂μ) = ∫ x, f x*(χ x*fderiv ℝ φ x v) ∂μ := by
    congr 1; ext x; ring
  rw [hi]
  simp only [Pi.mul_apply] at h
  linarith

lemma gradient_convolution {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (x : E) :
    gradient (f ⋆[lsmul ℝ ℝ,μ] K) x = (K ⋆[lsmul ℝ ℝ,μ] g) x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,(hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable (hK.of_le (by simp)) x).fderiv]
  rw [convolution_precompR_apply _ hf.locallyIntegrable (hc.fderiv ℝ) (hK.continuous_fderiv (by simp))]
  let ψ : E → ℝ := fun y => K (x-y)
  have hψ : ContDiff ℝ ∞ ψ := hK.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y) : fderiv ℝ ψ y v = -(fderiv ℝ K (x-y) v) := by
    have he := (hK.differentiable (by simp) (x-y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change fderiv ℝ (K ∘ (fun y => x-y)) y v = _
    rw [he.fderiv]
    simp
  have he := hw ψ hψ hcψ v
  simp_rw [hd,mul_neg] at he
  rw [integral_neg,neg_inj] at he
  have hi := (hc.convolutionExists_left (lsmul ℝ ℝ) hK.continuous hg.locallyIntegrable x).integrable_swap
  change Integrable (fun y => K (x-y) • g y) μ at hi
  calc
    _ = ∫ y, ⟪g y,v⟫ * K (x-y) ∂μ := he
    _ = ⟪∫ y, K (x-y) • g y ∂μ,v⟫ := by
      rw [real_inner_comm,← integral_inner (𝕜 := ℝ) hi]
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by simp only [real_inner_smul_right,real_inner_comm]; ring)
    _ = _ := by rw [convolution_eq_swap]; rfl

lemma norm_convolution_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : E → ℝ} {g : E → F}
    (hK : Integrable K μ) (hg : Integrable g μ) :
    (∫ x, ‖(K ⋆[lsmul ℝ ℝ,μ] g) x‖ ∂μ) ≤ (∫ x, |K x| ∂μ)*(∫ x, ‖g x‖ ∂μ) := by
  have hi := hK.norm.integrable_convolution (lsmul ℝ ℝ) hg.norm
  calc
    _ ≤ ∫ x, ( (fun y => ‖K y‖) ⋆[lsmul ℝ ℝ,μ] (fun y => ‖g y‖)) x ∂μ := by
      apply integral_mono_ae (hK.integrable_convolution (lsmul ℝ ℝ) hg).norm hi
      filter_upwards [hK.norm.ae_convolution_exists (lsmul ℝ ℝ) hg.norm] with x hx
      simp only [convolution_def,lsmul_apply,smul_eq_mul] at hx ⊢
      exact norm_integral_le_of_norm_le hx (ae_of_all _ (fun y => by rw [norm_smul]))
    _ = _ := by rw [integral_convolution _ hK.norm hg.norm]; simp only [lsmul_apply,smul_eq_mul,Real.norm_eq_abs]

end WeakSobolev

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution

/-- Scheffe's argument for vector-valued L1 functions, without an a priori
pointwise dominating function for the approximating sequence. -/
lemma norm_sub_tendsto_zero {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {f : α → F} {u : ℕ → α → F}
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, ‖u n x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ) :
    Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0) := by
  let d := fun n x => ‖u n x‖+‖f x‖-‖u n x-f x‖
  have hd0 (n x) : 0 ≤ d n x := sub_nonneg.mpr (norm_sub_le _ _)
  have hd2 (n x) : d n x ≤ 2*‖f x‖ := by
    have hn := norm_le_norm_sub_add (u n x) (f x)
    dsimp [d]; linarith
  have hdint (n) : Integrable (d n) μ := ((hu n).norm.add hf.norm).sub ((hu n).sub hf).norm
  have hdt : Tendsto (fun n => ∫ x, d n x ∂μ) atTop (𝓝 (2*∫ x, ‖f x‖ ∂μ)) := by
    rw [← integral_const_mul]
    apply tendsto_integral_of_dominated_convergence (fun x => 2*‖f x‖)
    · intro n; exact (hdint n).aestronglyMeasurable
    · exact hf.norm.const_mul 2
    · intro n; exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hd0 n x)]; exact hd2 n x)
    · filter_upwards [hlim] with x hx
      have he := (hx.norm.add (tendsto_const_nhds (x := ‖f x‖))).sub ((hx.sub (tendsto_const_nhds (x := f x))).norm)
      simpa only [sub_self,norm_zero,sub_zero,two_mul,d] using he
  have hle (n) : (∫ x, ‖u n x-f x‖ ∂μ) ≤ 2*(∫ x, ‖f x‖ ∂μ)-(∫ x, d n x ∂μ) := by
    have he : (∫ x, d n x ∂μ) = (∫ x, ‖u n x‖ ∂μ)+(∫ x, ‖f x‖ ∂μ)-(∫ x, ‖u n x-f x‖ ∂μ) := by
      exact (integral_sub ((hu n).norm.add hf.norm) ((hu n).sub hf).norm).trans (by simp only [Pi.add_apply, Pi.sub_apply]; rw [integral_add (hu n).norm hf.norm])
    rw [he]
    linarith [hbound n]
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hle
  simpa only [sub_self] using (tendsto_const_nhds (x := 2*∫ x, ‖f x‖ ∂μ)).sub hdt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mollifier_radius_tendsto : Tendsto (fun n => (mollifier (E := E) n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [mollifier,← mul_div_assoc,mul_one,mul_zero] using h

lemma smoothVector_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) : Integrable (smoothVector (μ := μ) f n) μ :=
  (mollifier n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf

lemma smoothVector_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) : ContDiff ℝ ∞ (smoothVector (μ := μ) f n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (mollifier n).contDiff_normed hf.locallyIntegrable

lemma smoothVector_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) :
    (∫ x, ‖smoothVector (μ := μ) f n x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
  have h := norm_convolution_le (mollifier n).integrable_normed hf
  simpa only [smoothVector,abs_of_nonneg ((mollifier n).nonneg_normed (μ := μ) _),(mollifier n).integral_normed,mul_one,one_mul] using h

lemma smoothVector_converges {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, ‖smoothVector (μ := μ) f n x-f x‖ ∂μ) atTop (𝓝 0) := by
  apply norm_sub_tendsto_zero hf (smoothVector_integrable hf)
  · exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable mollifier_radius_tendsto
      (Eventually.of_forall (fun n => (by dsimp [mollifier]; ring_nf; rfl : (mollifier (E := E) n).rOut ≤ 2*(mollifier n).rIn))) hf.locallyIntegrable
  · exact smoothVector_norm_le hf

lemma smooth_gradient {f : E → ℝ} {g : E → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : HasGradient (μ := μ) f g) (n : ℕ) :
    gradient (smooth (μ := μ) f n) = smoothVector (μ := μ) g n := by
  ext x
  have h := gradient_convolution hf hg hw ((mollifier n).contDiff_normed (μ := μ)) ((mollifier n).hasCompactSupport_normed (μ := μ)) x
  have he : f ⋆[lsmul ℝ ℝ,μ] (mollifier n).normed μ = (mollifier n).normed μ ⋆[lsmul ℝ ℝ,μ] f := by
    ext z
    rw [convolution_def, convolution_def]
    simp only [lsmul_apply, smul_eq_mul]
    rw [← integral_sub_left_eq_self (fun y => f y * (mollifier n).normed μ (z-y)) μ z]
    simp only [sub_sub_cancel]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => mul_comm _ _)
  simpa only [smooth,smoothVector,he] using h

end WeakSobolev

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff (E := E) n) :=
  (mollifier 0).contDiff.comp (contDiff_const.smul contDiff_id)

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff (E := E) n) :=
  (mollifier 0).hasCompactSupport.comp_smul (by positivity)

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_bound (n : ℕ) (x : E) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 :=
  ⟨(mollifier 0).nonneg, (mollifier 0).le_one⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_tendsto (x : E) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ • x) atTop (𝓝 0) := by
    simpa only [one_div,zero_smul] using ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x)
  have h := ((mollifier (E := E) 0).continuous.tendsto 0).comp ht
  have he : (mollifier (E := E) 0) (0:E) = 1 := (mollifier 0).one_of_mem_closedBall (mem_closedBall_self (mollifier 0).rIn_pos.le)
  rw [he] at h
  convert h using 1
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma norm_gradient_fderiv (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

omit [MeasurableSpace E] [BorelSpace E] in
lemma cutoff_gradient_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ n x,
    ‖gradient (cutoff (E := E) n) x‖ ≤ L/((n:ℝ)+1) := by
  obtain ⟨L,hL⟩ := ((mollifier (E := E) 0).contDiff (n := (1:ℕ∞))).lipschitzWith_of_hasCompactSupport
    (mollifier 0).hasCompactSupport one_ne_zero
  refine ⟨L,L.coe_nonneg,?_⟩
  intro n x
  have he : LipschitzWith (L*‖((n:ℝ)+1)⁻¹‖₊) (cutoff (E := E) n) :=
    hL.comp (show LipschitzWith ‖((n:ℝ)+1)⁻¹‖₊ (fun x : E => ((n:ℝ)+1)⁻¹ • x) from
      lipschitzWith_smul (((n:ℝ)+1)⁻¹))
  rw [norm_gradient_fderiv]
  have hb := norm_fderiv_le_of_lipschitz ℝ he (x₀ := x)
  simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((n:ℝ)+1)⁻¹), div_eq_mul_inv] using hb

omit [μ.IsAddHaarMeasure] in
lemma cutoff_smul_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Integrable f μ) (n : ℕ) : Integrable (fun x => cutoff n x • f x) μ := by
  apply hf.bdd_smul 1 (cutoff_contDiff n).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_bound n x).1]; exact (cutoff_bound n x).2)

omit [μ.IsAddHaarMeasure] in
lemma cutoff_smul_converges {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, ‖cutoff n x • f x-f x‖ ∂μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫ x, ‖cutoff n x • f x-f x‖ ∂μ) atTop (𝓝 (∫ x, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro n; exact ((cutoff_smul_integrable hf n).sub hf).norm.aestronglyMeasurable
    · exact hf.norm
    · intro n
      exact ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _), show cutoff n x • f x-f x = (cutoff n x-1) • f x by rw [sub_smul,one_smul], norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (cutoff_bound n x).2)]
        nlinarith [(cutoff_bound n x).1,norm_nonneg (f x)])
    · exact ae_of_all _ (fun x => by
        have hh := ((cutoff_tendsto x).smul_const (f x)).sub (tendsto_const_nhds (x := f x)) |>.norm
        simpa only [one_smul,sub_self,norm_zero] using hh)
  simpa only [integral_zero] using ht

omit [μ.IsAddHaarMeasure] in
lemma cutoff_gradient_integrable {f : E → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => f x • gradient (cutoff (E := E) n) x) μ := by
  exact hf.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp ((cutoff_contDiff n).continuous_fderiv (by simp)))
    (by
      apply (cutoff_compact (E := E) n).fderiv ℝ |>.comp_left
      exact (InnerProductSpace.toDual ℝ E).symm.map_zero)

omit [μ.IsAddHaarMeasure] in
lemma cutoff_gradient_converges {f : E → ℝ} (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, ‖f x • gradient (cutoff (E := E) n) x‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨L,hL,hb⟩ := cutoff_gradient_bound (E := E)
  have ht : Tendsto (fun n : ℕ => (L/((n:ℝ)+1)) * ∫ x, ‖f x‖ ∂μ) atTop (𝓝 0) := by
    have hh := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul L).mul_const (∫ x, ‖f x‖ ∂μ)
    simpa only [mul_zero,zero_mul,mul_one_div] using hh
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ ht
  intro n
  rw [← integral_const_mul]
  apply integral_mono (cutoff_gradient_integrable hf n).norm (hf.norm.const_mul _)
  intro x
  dsimp only
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)

end WeakSobolev

namespace WeakSobolev
open ContinuousLinearMap
open scoped Convolution

lemma integral_norm_sub_triangle {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f g h : α → F} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, ‖f x-h x‖ ∂μ) ≤ (∫ x, ‖f x-g x‖ ∂μ)+(∫ x, ‖g x-h x‖ ∂μ) := by
  have he := integral_add (hf.sub hg).norm (hg.sub hh).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact integral_mono (hf.sub hh).norm ((hf.sub hg).norm.add (hg.sub hh).norm) (fun x => norm_sub_le_norm_sub_add_norm_sub _ _ _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] in
lemma cutGradient_integrable {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (n : ℕ) :
    Integrable (cutGradient f g n) μ :=
  (cutoff_smul_integrable hg n).add (cutoff_gradient_integrable hf n)

omit [μ.IsAddHaarMeasure] in
lemma cutGradient_converges {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, ‖cutGradient f g n x-g x‖ ∂μ) atTop (𝓝 0) := by
  have ht := (cutoff_smul_converges hg).add (cutoff_gradient_converges hf)
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ (by simpa only [zero_add] using ht)
  intro n
  have he := integral_add ((cutoff_smul_integrable hg n).sub hg).norm (cutoff_gradient_integrable hf n).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  apply integral_mono ((cutGradient_integrable hf hg n).sub hg).norm (((cutoff_smul_integrable hg n).sub hg).norm.add (cutoff_gradient_integrable hf n).norm)
  intro x
  change ‖cutoff n x • g x + f x • gradient (cutoff n) x - g x‖ ≤ ‖cutoff n x • g x - g x‖+‖f x • gradient (cutoff n) x‖
  simpa only [add_sub_right_comm] using norm_add_le (cutoff n x • g x-g x) (f x • gradient (cutoff n) x)

/-- Strong W11 density obtained by truncation and normalized mollification.
Both approximations are genuine functions, not distributions defined by a new axiom. -/
theorem exists_smooth_compact_approx {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      (∫ x, ‖u x-f x‖ ∂μ) < ε ∧ (∫ x, ‖gradient u x-g x‖ ∂μ) < ε := by
  have h1 := (cutoff_smul_converges hf).eventually (gt_mem_nhds (half_pos hε))
  have h2 := (cutGradient_converges hf hg).eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨n,hn1,hn2⟩ := (h1.and h2).exists
  let f' : E → ℝ := fun x => cutoff n x*f x
  let g' : E → E := cutGradient f g n
  have hf' : Integrable f' μ := cutoff_smul_integrable hf n
  have hg' : Integrable g' μ := cutGradient_integrable hf hg n
  have hw' : HasGradient (μ := μ) f' g' := hw.mul_contDiff hf hg (cutoff_contDiff n) (cutoff_compact n)
  have hk1 := (smoothVector_converges hf').eventually (gt_mem_nhds (half_pos hε))
  have hk2 := (smoothVector_converges hg').eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨k,hk1,hk2⟩ := (hk1.and hk2).exists
  refine ⟨smooth (μ := μ) f' k, smoothVector_contDiff hf' k, ?_, ?_, ?_⟩
  · exact (mollifier k).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) (cutoff_compact n).mul_right
  · have hi := integral_norm_sub_triangle (smoothVector_integrable hf' k) hf' hf
    change (∫ x, ‖f' x-f x‖ ∂μ) < ε/2 at hn1
    change (∫ x, ‖smoothVector (μ := μ) f' k x-f x‖ ∂μ) < ε
    linarith
  · rw [smooth_gradient hf' hg' hw']
    have hi := integral_norm_sub_triangle (smoothVector_integrable hg' k) hg' hg
    change (∫ x, ‖g' x-g x‖ ∂μ) < ε/2 at hn2
    linarith

end WeakSobolev

namespace WeakSobolev
section L1
variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    {f : α → F} {u : ℕ → α → F}

lemma tendsto_eLpNorm_one (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n-f) 1 μ) atTop (𝓝 0) := by
  have he (n) : eLpNorm (u n-f) 1 μ = ENNReal.ofReal (∫ x, ‖u n x-f x‖ ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hu n).sub hf)]
    rfl
  simp_rw [he]
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim

lemma integral_converges_norm [NormedSpace ℝ F]
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, u n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_L1' f hf.aestronglyMeasurable (Eventually.of_forall hu) (tendsto_eLpNorm_one hf hu hlim)

lemma exists_ae_subseq (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ x ∂μ, Tendsto (fun n => u (s n) x) atTop (𝓝 (f x)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (fun n => (hu n).aestronglyMeasurable) hf.aestronglyMeasurable (tendsto_eLpNorm_one hf hu hlim)).exists_seq_tendsto_ae

lemma bounded_smul_converges [NormedSpace ℝ F]
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hlim : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0))
    {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {K : ℝ} (hK : ∀ᵐ x ∂μ, ‖φ x‖ ≤ K) :
    Tendsto (fun n => ∫ x, ‖φ x • u n x - φ x • f x‖ ∂μ) atTop (𝓝 0) := by
  have ht := hlim.const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun x => norm_nonneg _))) _ (by simpa only [mul_zero] using ht)
  exact Eventually.of_forall (fun n => by
    rw [← integral_const_mul]
    apply integral_mono_ae (( (hu n).bdd_smul K hφ hK).sub (hf.bdd_smul K hφ hK)).norm (((hu n).sub hf).norm.const_mul K)
    filter_upwards [hK] with x hx
    change ‖φ x • u n x-φ x • f x‖ ≤ K*‖u n x-f x‖
    rw [← smul_sub,norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))
end L1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

omit [BorelSpace E] in
lemma integral_inner_mul {φ : E → ℝ} {g : E → E}
    (hi : Integrable (fun x => φ x • g x) μ) (v : E) :
    (∫ x, ⟪g x,v⟫*φ x ∂μ) = ⟪∫ x, φ x • g x ∂μ,v⟫ := by
  rw [real_inner_comm,← integral_inner (𝕜 := ℝ) hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp only; rw [real_inner_smul_right,real_inner_comm]; ring)

/-- The distributional identity is closed under strong L1 convergence of both
functions and their genuine gradients. -/
lemma HasGradient.limit {f : E → ℝ} {g : E → E} {u : ℕ → E → ℝ} {v : ℕ → E → E}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hu : ∀ n, Integrable (u n) μ) (hv : ∀ n, Integrable (v n) μ)
    (hw : ∀ n, HasGradient (μ := μ) (u n) (v n))
    (huf : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0))
    (hvg : Tendsto (fun n => ∫ x, ‖v n x-g x‖ ∂μ) atTop (𝓝 0)) :
    HasGradient (μ := μ) f g := by
  intro φ hφ hc e
  let d : E → ℝ := fun x => fderiv ℝ φ x e
  have hd : Continuous d := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport d := hc.fderiv_apply ℝ e
  obtain ⟨D,hD⟩ := hd.norm.bddAbove_range_of_hasCompactSupport hdc.norm
  obtain ⟨K,hK⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hDb : ∀ᵐ x ∂μ, ‖d x‖ ≤ D := ae_of_all _ (fun x => hD (mem_range_self x))
  have hKb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ K := ae_of_all _ (fun x => hK (mem_range_self x))
  have ht1 := integral_converges_norm (hf.bdd_smul D hd.aestronglyMeasurable hDb)
    (fun n => (hu n).bdd_smul D hd.aestronglyMeasurable hDb)
    (bounded_smul_converges hf hu huf hd.aestronglyMeasurable hDb)
  have ht2 := integral_converges_norm (hg.bdd_smul K hφ.continuous.aestronglyMeasurable hKb)
    (fun n => (hv n).bdd_smul K hφ.continuous.aestronglyMeasurable hKb)
    (bounded_smul_converges hg hv hvg hφ.continuous.aestronglyMeasurable hKb)
  have he (n : ℕ) : (∫ x, d x • u n x ∂μ) = -⟪∫ x, φ x • v n x ∂μ,e⟫ := by
    rw [← integral_inner_mul ((hv n).bdd_smul K hφ.continuous.aestronglyMeasurable hKb)]
    simpa only [d,smul_eq_mul,mul_comm] using hw n φ hφ hc e
  have ht3 := (ht2.inner (𝕜 := ℝ) (tendsto_const_nhds (x := e))).neg
  have h := tendsto_nhds_unique ht1 (ht3.congr (fun n => (he n).symm))
  change (∫ x, d x • f x ∂μ) = -⟪∫ x, φ x • g x ∂μ,e⟫ at h
  rw [← integral_inner_mul (hg.bdd_smul K hφ.continuous.aestronglyMeasurable hKb)] at h
  simpa only [d,smul_eq_mul,mul_comm] using h

end WeakSobolev

namespace WeakSobolev
section Coefficients
variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {g : α → F} {v : ℕ → α → F}
lemma varying_smul_converges
    (hg : Integrable g μ) (hv : ∀ n, Integrable (v n) μ)
    (hvg : Tendsto (fun n => ∫ x, ‖v n x-g x‖ ∂μ) atTop (𝓝 0))
    {c : α → ℝ} {d : ℕ → α → ℝ} {K : ℝ} (_hK : 0 ≤ K)
    (hc : AEStronglyMeasurable c μ) (hd : ∀ n, AEStronglyMeasurable (d n) μ)
    (hcb : ∀ᵐ x ∂μ, ‖c x‖ ≤ K) (hdb : ∀ n, ∀ᵐ x ∂μ, ‖d n x‖ ≤ K)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => d n x) atTop (𝓝 (c x))) :
    Tendsto (fun n => ∫ x, ‖d n x • v n x-c x • g x‖ ∂μ) atTop (𝓝 0) := by
  have hi (n) : Integrable (fun x => ‖(d n x-c x) • g x‖) μ :=
    ((hg.bdd_smul K (hd n) (hdb n)).sub (hg.bdd_smul K hc hcb)).norm.congr
      (ae_of_all _ (fun x => by dsimp only; rw [sub_smul]; rfl))
  have ht1 : Tendsto (fun n => ∫ x, ‖(d n x-c x) • g x‖ ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => 2*K*‖g x‖)
      (fun n => (hi n).aestronglyMeasurable) (hg.norm.const_mul (2*K))
      (fun n => by
        filter_upwards [hdb n,hcb] with x hx hy
        rw [norm_norm,norm_smul]
        exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by linarith)) (norm_nonneg _))
      (hlim.mono (fun x hx => by simpa using ((hx.sub tendsto_const_nhds).smul_const (g x)).norm))
    simpa using ht
  have ht2 : Tendsto (fun n => K*(∫ x, ‖v n x-g x‖ ∂μ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hvg.const_mul K
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun x => norm_nonneg _))) _ (by simpa only [zero_add] using ht1.add ht2)
  exact Eventually.of_forall (fun n => by
    have he := integral_add (hi n) (((hv n).sub hg).norm.const_mul K)
    simp only [Pi.sub_apply] at he
    rw [← integral_const_mul,← he]
    apply integral_mono_ae (((hv n).bdd_smul K (hd n) (hdb n)).sub (hg.bdd_smul K hc hcb)).norm
      ((hi n).add (((hv n).sub hg).norm.const_mul K))
    filter_upwards [hdb n] with x hx
    change ‖d n x • v n x-c x • g x‖ ≤ ‖(d n x-c x) • g x‖+K*‖v n x-g x‖
    calc
      _ = ‖(d n x-c x) • g x+d n x • (v n x-g x)‖ := by congr 1; module
      _ ≤ ‖(d n x-c x) • g x‖+‖d n x • (v n x-g x)‖ := norm_add_le _ _
      _ ≤ _ := by
        have hh : ‖d n x • (v n x-g x)‖ ≤ K*‖v n x-g x‖ := by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        exact add_le_add le_rfl hh)
end Coefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma exists_smooth_sequence {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g) :
    ∃ u : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (u n) ∧ HasCompactSupport (u n)) ∧
      Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, ‖gradient (u n) x-g x‖ ∂μ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 (f x))) := by
  have hex (n : ℕ) := exists_smooth_compact_approx hf hg hw (by positivity : 0 < 1/((n:ℝ)+1))
  choose u hu hc hf' hg' using hex
  have ht : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht1 := squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) (fun n => (hf' n).le) ht
  have ht2 := squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) (fun n => (hg' n).le) ht
  have hi (n) : Integrable (u n) μ := (hu n).continuous.integrable_of_hasCompactSupport (hc n)
  obtain ⟨s,hs,ha⟩ := exists_ae_subseq hf hi ht1
  exact ⟨fun n => u (s n),fun n => ⟨hu _,hc _⟩,ht1.comp hs.tendsto_atTop,ht2.comp hs.tendsto_atTop,ha⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradient_scalar_comp {u : E → ℝ} {Φ : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hΦ : Differentiable ℝ Φ) (x : E) :
    gradient (Φ ∘ u) x = deriv Φ (u x) • gradient u x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [fderiv_comp x (hΦ _) (hu _)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [(hΦ _).hasDerivAt.hasFDerivAt.fderiv]
  change fderiv ℝ u x v * deriv Φ (u x) = deriv Φ (u x) * fderiv ℝ u x v
  ring

lemma HasGradient.scalar_comp {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) {K : ℝ≥0} (hK : LipschitzWith K Φ) (h0 : Φ 0 = 0) :
    HasGradient (μ := μ) (Φ ∘ f) (fun x => deriv Φ (f x) • g x) := by
  obtain ⟨u,hu,huf,hvg,ha⟩ := exists_smooth_sequence hf hg hw
  have hi (n) : Integrable (u n) μ := (hu n).1.continuous.integrable_of_hasCompactSupport (hu n).2
  have hgi (n) : Integrable (gradient (u n)) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp ((hu n).1.continuous_fderiv (by simp))).integrable_of_hasCompactSupport
      (((hu n).2.fderiv ℝ).comp_left (map_zero _))
  have hid : Integrable (Φ ∘ f) μ := memLp_one_iff_integrable.mp (hK.comp_memLp h0 (memLp_one_iff_integrable.mpr hf))
  have hδ := hΦ.continuous_deriv le_rfl
  have hδb (x : ℝ) : ‖deriv Φ x‖ ≤ (K:ℝ) := norm_deriv_le_of_lipschitz hK
  have hgrad : Integrable (fun x => deriv Φ (f x) • g x) μ :=
    hg.bdd_smul K (hδ.comp_aestronglyMeasurable hf.aestronglyMeasurable) (ae_of_all _ (fun x => hδb _))
  have hvi (n) : Integrable (fun x => deriv Φ (u n x) • gradient (u n) x) μ :=
    (hgi n).bdd_smul K ((hδ.comp (hu n).1.continuous).aestronglyMeasurable) (ae_of_all _ (fun x => hδb _))
  apply HasGradient.limit (u := fun n => Φ ∘ u n) (v := fun n x => deriv Φ (u n x) • gradient (u n) x) hid hgrad (fun n => memLp_one_iff_integrable.mp (hK.comp_memLp h0 (memLp_one_iff_integrable.mpr (hi n)))) hvi
  · intro n
    exact (contDiff_hasGradient (μ := μ) (hΦ.comp ((hu n).1.of_le (by simp)))).congr_ae
      (EventuallyEq.rfl) (ae_of_all _ (fun x => gradient_scalar_comp ((hu n).1.differentiable (by simp)) (hΦ.differentiable one_ne_zero) x))
  · apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ (by simpa only [mul_zero] using huf.const_mul (K:ℝ))
    intro n
    rw [← integral_const_mul]
    exact integral_mono ((memLp_one_iff_integrable.mp (hK.comp_memLp h0 (memLp_one_iff_integrable.mpr (hi n)))).sub hid).norm
      (((hi n).sub hf).norm.const_mul (K:ℝ)) (fun x => hK.norm_sub_le _ _)
  · exact varying_smul_converges hg hgi hvg K.coe_nonneg
      (hδ.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (fun n => (hδ.comp (hu n).1.continuous).aestronglyMeasurable)
      (ae_of_all _ (fun x => hδb _)) (fun n => ae_of_all _ (fun x => hδb _))
      (ha.mono (fun x hx => (hδ.tendsto _).comp hx))
end WeakSobolev

namespace WeakSobolev
lemma smoothAbs_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (smoothAbs ε) := by
  exact ((contDiff_id.pow 2).add contDiff_const).sqrt (fun x => ne_of_gt (by positivity)) |>.sub contDiff_const
lemma smoothAbs_hasDerivAt {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (smoothAbs ε) (x/Real.sqrt (x^2+ε^2)) x := by
  have he : x^2+ε^2 ≠ 0 := ne_of_gt (by positivity)
  have hd := ((((hasDerivAt_id x).pow 2).add_const (ε^2)).sqrt he).sub_const ε
  change HasDerivAt (fun y => Real.sqrt (y^2+ε^2)-ε) _ x
  simpa [mul_div_mul_left x (Real.sqrt (x^2+ε^2)) (by norm_num : (2:ℝ) ≠ 0)] using hd
lemma smoothAbs_deriv {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (smoothAbs ε) x = x/Real.sqrt (x^2+ε^2) := (smoothAbs_hasDerivAt hε x).deriv
lemma smoothAbs_deriv_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖deriv (smoothAbs ε) x‖ ≤ 1 := by
  rw [smoothAbs_deriv hε,Real.norm_eq_abs,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by positivity))).2
  rw [one_mul]
  have h := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε) : x^2 ≤ x^2+ε^2)
  simpa only [Real.sqrt_sq_eq_abs] using h
lemma smoothAbs_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (smoothAbs ε) :=
  lipschitzWith_of_nnnorm_deriv_le (fun x => (smoothAbs_hasDerivAt hε x).differentiableAt)
    (fun x => by exact_mod_cast smoothAbs_deriv_bound hε x)
lemma smoothAbs_zero {ε : ℝ} (hε : 0 ≤ ε) : smoothAbs ε 0 = 0 := by
  simp [smoothAbs,Real.sqrt_sq,hε]
lemma smoothAbs_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ‖smoothAbs ε x‖ ≤ ‖x‖ := by
  simpa only [smoothAbs_zero hε.le,sub_zero,NNReal.coe_one,one_mul] using (smoothAbs_lipschitz hε).norm_sub_le x 0
lemma smoothAbs_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => smoothAbs (1/((n:ℝ)+1)) x) atTop (𝓝 |x|) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ht := ((tendsto_const_nhds (x := x^2)).add (h.pow 2)).sqrt |>.sub h
  simpa only [smoothAbs,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero,sub_zero,Real.sqrt_sq_eq_abs] using ht

lemma absCoefficient_bound (x : ℝ) : ‖absCoefficient x‖ ≤ 1 := by
  by_cases hx : x=0
  · simp [absCoefficient,hx]
  · simp [absCoefficient,Real.norm_eq_abs,abs_abs,abs_ne_zero.mpr hx]
lemma absCoefficient_measurable : Measurable absCoefficient := measurable_id.div measurable_id.abs
lemma smoothAbs_deriv_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => deriv (smoothAbs (1/((n:ℝ)+1))) x) atTop (𝓝 (absCoefficient x)) := by
  have he (n : ℕ) : deriv (smoothAbs (1/((n:ℝ)+1))) x = x/Real.sqrt (x^2+(1/((n:ℝ)+1))^2) := smoothAbs_deriv (by positivity) x
  simp_rw [he]
  by_cases hx : x=0
  · simp [hx,absCoefficient]
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ht := (tendsto_const_nhds (x := x)).div (((tendsto_const_nhds (x := x^2)).add (h.pow 2)).sqrt)
      (by simpa only [zero_pow (by norm_num : (2:ℕ) ≠0),add_zero,Real.sqrt_sq_eq_abs] using abs_ne_zero.mpr hx)
    change Tendsto (fun n : ℕ => x / Real.sqrt (x^2+(1/((n:ℝ)+1))^2)) atTop
      (𝓝 (x / Real.sqrt (x^2+0^2))) at ht
    simpa only [zero_pow (by norm_num : (2:ℕ) ≠0),add_zero,Real.sqrt_sq_eq_abs,absCoefficient] using ht

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma HasGradient.abs {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) (hw : HasGradient (μ := μ) f g) :
    HasGradient (μ := μ) (fun x => |f x|) (fun x => absCoefficient (f x) • g x) := by
  let ε : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hc : AEStronglyMeasurable (fun x => absCoefficient (f x)) μ :=
    (absCoefficient_measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  have hcb : ∀ᵐ x ∂μ, ‖absCoefficient (f x)‖ ≤ (1:ℝ) := ae_of_all _ (fun x => absCoefficient_bound _)
  have hi (n) : Integrable (smoothAbs (ε n) ∘ f) μ :=
    memLp_one_iff_integrable.mp ((smoothAbs_lipschitz (hε n)).comp_memLp (smoothAbs_zero (hε n).le) (memLp_one_iff_integrable.mpr hf))
  have hv (n) : Integrable (fun x => deriv (smoothAbs (ε n)) (f x) • g x) μ :=
    hg.bdd_smul 1 (((smoothAbs_contDiff (hε n)).continuous_deriv le_rfl).comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (ae_of_all _ (fun x => smoothAbs_deriv_bound (hε n) _))
  apply HasGradient.limit (u := fun n => smoothAbs (ε n) ∘ f)
    (v := fun n x => deriv (smoothAbs (ε n)) (f x) • g x) hf.abs (hg.bdd_smul 1 hc hcb) hi hv
  · intro n
    exact hw.scalar_comp hf hg (smoothAbs_contDiff (hε n)) (smoothAbs_lipschitz (hε n)) (smoothAbs_zero (hε n).le)
  · have ht := tendsto_integral_of_dominated_convergence (fun x => 2*‖f x‖)
      (fun n => ((hi n).sub hf.abs).norm.aestronglyMeasurable) (hf.norm.const_mul 2)
      (fun n => ae_of_all _ (fun x => by
        change ‖‖smoothAbs (ε n) (f x)-|f x|‖‖ ≤ 2*‖f x‖
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by simpa only [Real.norm_eq_abs,abs_abs,two_mul] using add_le_add (smoothAbs_bound (hε n) (f x)) (le_refl |f x|))))
      (ae_of_all _ (fun x => by simpa only [ε,Function.comp_apply,Pi.sub_apply,sub_self,norm_zero] using ((smoothAbs_tendsto (f x)).sub (tendsto_const_nhds (x := |f x|))).norm))
    simpa using ht
  · apply varying_smul_converges hg (fun _ => hg) (by simp) zero_le_one hc
      (fun n => ((smoothAbs_contDiff (hε n)).continuous_deriv le_rfl).comp_aestronglyMeasurable hf.aestronglyMeasurable)
      hcb (fun n => ae_of_all _ (fun x => smoothAbs_deriv_bound (hε n) _))
    exact ae_of_all _ (fun x => smoothAbs_deriv_tendsto (f x))

omit [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma abs_gradient_bound {f : E → ℝ} {g : E → E}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => absCoefficient (f x) • g x) μ ∧
      (∫ x, ‖absCoefficient (f x) • g x‖ ∂μ) ≤ ∫ x, ‖g x‖ ∂μ := by
  have hi := hg.bdd_smul 1 ((absCoefficient_measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable)
    (ae_of_all _ (fun x => absCoefficient_bound (f x)))
  refine ⟨hi,integral_mono hi.norm hg.norm (fun x => ?_)⟩
  rw [norm_smul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (absCoefficient_bound (f x)) (norm_nonneg (g x))
end WeakSobolev

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace WeakCompact
open CompactlySupported CompactlySupportedContinuousMap

variable {X : Type*} [TopologicalSpace X]
    (Λ : ℕ → (C_c(X, ℝ) →ₚ[ℝ] ℝ)) {B : ℝ}
    (hb : ∀ n (f : C_c(X, ℝ)), |Λ n f| ≤ B*‖f.toBoundedContinuousFunction‖)

include hb

lemma limit_bound (f : C_c(X, ℝ)) : |limitPositive Λ hb f| ≤ B*‖f.toBoundedContinuousFunction‖ :=
  le_of_tendsto (limit_tendsto Λ hb f).abs (Eventually.of_forall (fun n => hb n f))

variable [T2Space X] [MeasurableSpace X] [BorelSpace X] [LocallyCompactSpace X]

lemma integral_limitMeasure (f : C_c(X, ℝ)) :
    Tendsto (fun n => Λ n f) (hyperfilter ℕ) (𝓝 (∫ x, f x ∂limitMeasure Λ hb)) := by
  rw [limitMeasure,RealRMK.integral_rieszMeasure]
  exact limit_tendsto Λ hb f

lemma limitMeasure_compact_bound (hB : 0 ≤ B) {K : Set X} (hK : IsCompact K) :
    limitMeasure Λ hb K ≤ ENNReal.ofReal B := by
  obtain ⟨f,hf1,hfc,-,hf⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  let f' : C_c(X, ℝ) := ⟨f,hfc⟩
  have hm := RealRMK.rieszMeasure_le_of_eq_one (limitPositive Λ hb) (f := f') (fun x => (hf x).1) hK hf1
  have hn : ‖f'.toBoundedContinuousFunction‖ ≤ 1 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).mpr
    intro x
    change ‖f x‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (hf x).1]
    exact (hf x).2
  have he : limitPositive Λ hb f' ≤ B :=
    (le_abs_self _).trans ((limit_bound Λ hb f').trans ((mul_le_mul_of_nonneg_left hn hB).trans_eq (mul_one B)))
  exact hm.trans (ENNReal.ofReal_le_ofReal he)

lemma limitMeasure_finite_bound (hB : 0 ≤ B) : limitMeasure Λ hb univ ≤ ENNReal.ofReal B := by
  have : (limitMeasure Λ hb).Regular := RealRMK.regular_rieszMeasure _
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  exact iSup_le (fun K => iSup_le (fun _ => iSup_le (fun hK => limitMeasure_compact_bound Λ hb hB hK)))

end WeakCompact

namespace WeakSobolev
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma gradient_l1_eq {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm (fderiv ℝ u) 1 μ = ENNReal.ofReal (∫ x, ‖gradient u x‖ ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm
    ((hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ))]
  simp only [gradient,(InnerProductSpace.toDual ℝ E).symm.norm_map]

lemma smooth_sobolev_two (hd : Module.finrank ℝ E = 2)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    eLpNorm u 2 μ ≤ (MeasureTheory.eLpNormLESNormFDerivOneConst μ 2 : ℝ≥0∞) *
      ENNReal.ofReal (∫ x, ‖gradient u x‖ ∂μ) := by
  have hp : NNReal.HolderConjugate (Module.finrank ℝ E) 2 := by
    rw [hd]
    exact NNReal.HolderConjugate.two_two
  simpa only [gradient_l1_eq hu hc,ENNReal.coe_ofNat,NNReal.coe_ofNat] using
    MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one μ hu hc hp

lemma gradient_integral_le {u : E → ℝ} {g : E → E}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (hg : Integrable g μ) :
    (∫ x, ‖gradient u x‖ ∂μ) ≤ (∫ x, ‖g x‖ ∂μ)+(∫ x, ‖gradient u x-g x‖ ∂μ) := by
  have hi : Integrable (gradient u) μ :=
    ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.integrable_comp
      ((hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hc.fderiv ℝ)))
  have he := integral_add hg.norm (hi.sub hg).norm
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact integral_mono hi.norm (hg.norm.add (hi.sub hg).norm) (fun x => by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (g x) (gradient u x))

/-- The planar Sobolev embedding extended by genuine strong W11 density.
The harmless slack one is used only for finiteness/local convergence. -/
lemma sobolev_two_le (hd : Module.finrank ℝ E = 2)
    {f : E → ℝ} {g : E → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : HasGradient (μ := μ) f g) :
    eLpNorm f 2 μ ≤ (MeasureTheory.eLpNormLESNormFDerivOneConst μ 2 : ℝ≥0∞) *
      ENNReal.ofReal ((∫ x, ‖g x‖ ∂μ)+1) := by
  obtain ⟨u,hu,-,ht,ha⟩ := exists_smooth_sequence hf hg hw
  apply Lp.eLpNorm_le_of_ae_tendsto _ (fun n => (hu n).1.continuous.aestronglyMeasurable) ha
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  apply (smooth_sobolev_two hd ((hu n).1.of_le (by simp)) (hu n).2).trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact (gradient_integral_le ((hu n).1.of_le (by simp)) (hu n).2 hg).trans (by linarith)

lemma memLp_two (hd : Module.finrank ℝ E = 2)
    {f : E → ℝ} {g : E → E} (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : HasGradient (μ := μ) f g) : MemLp f 2 μ :=
  ⟨hf.aestronglyMeasurable, (sobolev_two_le hd hf hg hw).trans_lt (by finiteness)⟩

lemma lipschitz_hasGradient {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasGradient (μ := μ) f (gradient f) := by
  intro φ hφ hc v
  obtain ⟨K,hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  exact _root_.OAI.LipschitzWith.integral_mul_fderiv_eq_neg hf hK hc v
end WeakSobolev

namespace DiskMaximalTools
lemma rationalMaximal_ae_finite (ν : Measure ℂ) [IsFiniteMeasure ν] :
    ∀ᵐ x, rationalMaximal ν x ≠ ⊤ := by
  rw [ae_iff]
  simp only [not_not]
  change volume {x | rationalMaximal ν x = ⊤} = 0
  apply le_antisymm _ (bot_le)
  have ht := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
    (a := (25:ℝ≥0∞)) (Or.inr (by norm_num))
  have ht' := ENNReal.Tendsto.mul_const ht (b := ν univ) (Or.inr (measure_ne_top _ _))
  simp only [mul_zero,zero_mul] at ht'
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have h := weak_rationalMaximal (ν := ν) (by exact_mod_cast hn : (0:ℝ)<n)
  have hs : {x | rationalMaximal ν x = ⊤} ⊆ {x | ENNReal.ofReal (n:ℝ)<rationalMaximal ν x} := by
    intro x hx
    change ENNReal.ofReal (n:ℝ) < rationalMaximal ν x
    rw [hx]
    exact ENNReal.ofReal_lt_top
  simpa only [ENNReal.ofReal_natCast,div_eq_mul_inv] using (measure_mono hs).trans h

lemma absoluteMeasure_finite {f : ℂ → ℝ} (hf : Integrable f) : IsFiniteMeasure (absoluteMeasure f) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ (fun x => abs_nonneg (f x)))]
  exact ENNReal.ofReal_ne_top

lemma absoluteMeasure_congr {f g : ℂ → ℝ} (h : f =ᵐ[volume] g) : absoluteMeasure f = absoluteMeasure g :=
  withDensity_congr_ae (h.mono (fun x hx => by simp only [hx]))

lemma memLp_maximalComplexReal_of_measurable {f : ℂ → ℝ} (hm : Measurable f)
    (hf : Integrable f) (hp : MemLp f 2) : MemLp (maximalComplexReal f) 2 := by
  let _ := absoluteMeasure_finite hf
  have hmax : AEStronglyMeasurable (maximalComplexReal f) volume :=
    (measurable_rationalMaximal _).ennreal_toReal.aestronglyMeasurable
  refine ⟨hmax, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)]
  let _ : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal |f x|)) := absoluteMeasure_finite hf
  have h := strong_rationalMaximal hm.abs (fun x => abs_nonneg (f x)) (by norm_num : (1:ℝ)<2)
  have hi := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num) hp.eLpNorm_lt_top
  simp only [ENNReal.toReal_ofNat, ← ofReal_norm,Real.norm_eq_abs,
    ] at hi
  have hi' : ∫⁻ x, ENNReal.ofReal (|f x| ^ (2:ℝ)) < (⊤:ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0:ℝ)≤2)] using hi
  have ht := h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hi')
  simpa only [maximalComplexReal,maximalComplex,absoluteMeasure,ENNReal.toReal_ofNat,
    ← ofReal_norm,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num : (0:ℝ)≤2)] using ht

lemma memLp_maximalComplexReal {f : ℂ → ℝ} (hf : Integrable f) (hp : MemLp f 2) :
    MemLp (maximalComplexReal f) 2 := by
  let g := hf.aestronglyMeasurable.mk f
  have he : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hm : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have h := memLp_maximalComplexReal_of_measurable hm (hf.congr he) (hp.ae_eq he)
  have heM : maximalComplexReal f = maximalComplexReal g := by
    unfold maximalComplexReal maximalComplex
    rw [absoluteMeasure_congr he]
  rwa [heM]

lemma maximalComplex_ae_finite {f : ℂ → ℝ} (hf : Integrable f) :
    ∀ᵐ x, maximalComplex f x ≠ ⊤ := by
  let _ := absoluteMeasure_finite hf
  exact rationalMaximal_ae_finite _

lemma maximalComplex_eq_all_radii (f : ℂ → ℝ) (x : ℂ) :
    maximalComplex f x = ⨆ (r : ℝ) (_ : 0<r), absoluteMeasure f (Metric.ball x r)/volume (Metric.ball x r) := by
  apply le_antisymm
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le (q:ℝ) (le_iSup_of_le (by exact_mod_cast hq : (0:ℝ)<q) le_rfl)
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    exact disk_average_le_rationalMaximal_exact _ x hr
end DiskMaximalTools

namespace WeakSobolev
lemma integral_norm_converges {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {f : α → F} {u : ℕ → α → F}
    (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (ht : Tendsto (fun n => ∫ x, ‖u n x-f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖u n x‖ ∂μ) atTop (𝓝 (∫ x, ‖f x‖ ∂μ)) := by
  apply integral_converges_norm hf.norm (fun n => (hu n).norm)
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ ht
  intro n
  apply integral_mono ((hu n).norm.sub hf.norm).norm ((hu n).sub hf).norm
  intro x
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using abs_norm_sub_norm_le (u n x) (f x)
end WeakSobolev

namespace SobolevBand
open DiskMoments RadiusEnvelope

lemma average_abs_le {f : ℂ → ℝ} (hf : Integrable f) {a t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (x : ℂ) :
    |signedAverage f x t| ≤ (∫ y, ‖f y‖)/(Real.pi*a^2) := by
  have ht : 0 < t := ha.trans_le hat
  have hden : 0 < Real.pi*a^2 := mul_pos Real.pi_pos (sq_pos_of_pos ha)
  rw [signedAverage,abs_div,abs_of_pos (mul_pos Real.pi_pos (sq_pos_of_pos ht))]
  have he : |∫ y in Metric.ball x t, f y| ≤ ∫ y, ‖f y‖ := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm f).trans
      (setIntegral_le_integral hf.norm (ae_of_all _ (fun y => norm_nonneg (f y))))
  apply (div_le_div_of_nonneg_right he (by positivity : 0≤Real.pi*t^2)).trans
  exact div_le_div_of_nonneg_left (integral_nonneg (fun y => norm_nonneg (f y))) hden
    (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) Real.pi_pos.le)

lemma average_sub {f h : ℂ → ℝ} (hf : Integrable f) (hh : Integrable h) (x : ℂ) (t : ℝ) :
    signedAverage f x t-signedAverage h x t = signedAverage (f-h) x t := by
  simp only [signedAverage,Pi.sub_apply,integral_sub hf.integrableOn hh.integrableOn,sub_div]

lemma values_bdd {f : ℂ → ℝ} (hf : Integrable f) {a b : ℝ} (ha : 0 < a) (x : ℂ) :
    BddAbove ((fun r => signedAverage f x r) '' Icc a b) := by
  refine ⟨(∫ y, ‖f y‖)/(Real.pi*a^2),?_⟩
  rintro _ ⟨r,hr,rfl⟩
  exact (le_abs_self _).trans (average_abs_le hf ha hr.1 x)

lemma average_le_band {f : ℂ → ℝ} (hf : Integrable f) {a b r : ℝ}
    (ha : 0<a) (hr : r ∈ Icc a b) (x : ℂ) : signedAverage f x r ≤ band f a b x :=
  le_csSup (values_bdd hf ha x) (mem_image_of_mem _ hr)

lemma band_le {f : ℂ → ℝ} {a b M : ℝ} (hab : a ≤ b) (x : ℂ)
    (hM : ∀ r ∈ Icc a b, signedAverage f x r ≤ M) : band f a b x ≤ M := by
  apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
  rintro _ ⟨r,hr,rfl⟩
  exact hM r hr

lemma band_sub_le {f h : ℂ → ℝ} (hf : Integrable f) (hh : Integrable h)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (x : ℂ) :
    |band f a b x-band h a b x| ≤ (∫ y, ‖f y-h y‖)/(Real.pi*a^2) := by
  have he (f h : ℂ → ℝ) (hf : Integrable f) (hh : Integrable h) :
      band f a b x ≤ band h a b x+(∫ y, ‖f y-h y‖)/(Real.pi*a^2) := by
    apply band_le hab x
    intro r hr
    have hs := average_abs_le (hf.sub hh) ha hr.1 x
    rw [← average_sub hf hh] at hs
    have hl := average_le_band hh ha hr x
    simp only [Pi.sub_apply] at hs
    linarith [le_abs_self (signedAverage f x r-signedAverage h x r)]
  rw [abs_le]
  constructor
  · have he' := he h f hh hf
    simp only [norm_sub_rev (h _) (f _)] at he'
    linarith
  · linarith [he f h hf hh]

lemma smooth_average_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a t : ℝ} (ha : 0<a) (hat : a≤t) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (fun x => signedAverage f x t) := by
  obtain ⟨L,hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hD := fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)
  have hi : Integrable (gradient f) := (continuous_gradient hf).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  have ht := ha.trans_le hat
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hasFDerivAt_signedAverage hf hD x ht).differentiableAt)
  intro x
  change ‖fderiv ℝ (fun x => signedAverage f x t) x‖ ≤ _
  rw [← (InnerProductSpace.toDual ℝ ℂ).symm.norm_map]
  change ‖gradient (fun x => signedAverage f x t) x‖ ≤ _
  rw [gradient_signedAverage hf hD x ht,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(Real.pi*t^2)⁻¹)]
  have he : ‖∫ y in Metric.ball x t, gradient f y‖ ≤ ∫ y, ‖gradient f y‖ :=
    (norm_integral_le_integral_norm _).trans (setIntegral_le_integral hi.norm (ae_of_all _ (fun y => norm_nonneg _)))
  rw [← div_eq_inv_mul]
  exact (div_le_div_of_nonneg_right he (by positivity)).trans
    (div_le_div_of_nonneg_left (integral_nonneg (fun y => norm_nonneg _)) (by positivity)
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ ha.le ht.le |>.mpr hat) Real.pi_pos.le))

lemma smooth_band_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    LipschitzWith (⟨(∫ y, ‖gradient f y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (band f a b) :=
  RadiusEnvelope.lipschitz hab (fun x => signedAverage_radius_continuousOn hf x ha)
    (fun _ hr => smooth_average_lipschitz hf hc ha hr.1)

lemma band_converges {f : ℂ → ℝ} {u : ℕ → ℂ → ℝ} (hf : Integrable f) (hu : ∀ n, Integrable (u n))
    (ht : Tendsto (fun n => ∫ x, ‖u n x-f x‖) atTop (𝓝 0))
    {a b : ℝ} (ha : 0<a) (hab : a≤b) (x : ℂ) :
    Tendsto (fun n => band (u n) a b x) atTop (𝓝 (band f a b x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using band_sub_le (hu n) hf ha hab x)
  simpa only [zero_div,Real.norm_eq_abs] using ht.div_const (Real.pi*a^2)

lemma band_lipschitz {f : ℂ → ℝ} {g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hw : WeakSobolev.HasGradient (μ := volume) f g) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    LipschitzWith (⟨(∫ y, ‖g y‖)/(Real.pi*a^2),by positivity⟩ : ℝ≥0) (band f a b) := by
  obtain ⟨u,hu,huf,hvg,-⟩ := WeakSobolev.exists_smooth_sequence hf hg hw
  have hi (n) : Integrable (u n) := (hu n).1.continuous.integrable_of_hasCompactSupport (hu n).2
  have hgi (n) : Integrable (gradient (u n)) :=
    (continuous_gradient ((hu n).1.of_le (by simp))).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hgt := WeakSobolev.integral_norm_converges hg hgi hvg
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply le_of_tendsto_of_tendsto ((band_converges hf hi huf ha hab x).dist (band_converges hf hi huf ha hab y))
    ((hgt.div_const (Real.pi*a^2)).mul_const (dist x y))
  exact Eventually.of_forall (fun n => (smooth_band_lipschitz ((hu n).1.of_le (by simp)) (hu n).2 ha hab).dist_le_mul x y)
end SobolevBand

namespace WeakCompact
open CompactlySupported CompactlySupportedContinuousMap
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {μ : Measure X}

omit [T2Space X] [LocallyCompactSpace X] in
lemma density_test_le_set {w : X → ℝ} (hw : Integrable w μ) (h0 : ∀ᵐ x ∂μ, 0≤w x)
    (φ : C_c(X,ℝ)) {O : Set X} (hO : MeasurableSet O) (hs : tsupport φ ⊆ O)
    (hφ : ∀ x, φ x≤1) : (∫ x,w x*φ x ∂μ) ≤ ∫ x in O,w x ∂μ := by
  rw [← integral_indicator hO]
  apply integral_mono_ae (density_test_integrable hw φ) (hw.indicator hO)
  filter_upwards [h0] with x hx
  by_cases hxo : x∈O
  · rw [indicator_of_mem hxo]
    exact mul_le_of_le_one_right hx (hφ x)
  · rw [indicator_of_notMem hxo,image_eq_zero_of_notMem_tsupport (fun h => hxo (hs h)),mul_zero]

variable (w : ℕ → X → ℝ) (hw : ∀ n, Integrable (w n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0≤w n x)
  {B : ℝ} (hb : ∀ n, (∫ x,w n x ∂μ) ≤ B)

lemma densityLimit_integral (φ : C_c(X,ℝ)) :
    Tendsto (fun n => ∫ x,w n x*φ x ∂μ) (hyperfilter ℕ) (𝓝 (∫ x,φ x ∂densityLimit w hw h0 hb)) :=
  integral_limitMeasure _ _ φ

lemma densityLimit_mass (hB : 0≤B) : densityLimit w hw h0 hb univ ≤ ENNReal.ofReal B :=
  limitMeasure_finite_bound _ _ hB

lemma densityLimit_regular : (densityLimit w hw h0 hb).Regular := RealRMK.regular_rieszMeasure _
lemma densityLimit_finite (hB : 0≤B) : IsFiniteMeasure (densityLimit w hw h0 hb) :=
  ⟨(densityLimit_mass w hw h0 hb hB).trans_lt ENNReal.ofReal_lt_top⟩

/-- The local lower-semicontinuity estimate needed for null-set localization.
Only eventual bounds are required, so large-radius splitting may start late. -/
lemma densityLimit_compact_bound {D : ℝ} {K O : Set X} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hD : ∀ᶠ n in atTop, (∫ x in O,w n x ∂μ) ≤ D) :
    densityLimit w hw h0 hb K ≤ ENNReal.ofReal D := by
  obtain ⟨φ,hφ1,hφc,hφs,hφ⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  let φ' : C_c(X,ℝ) := ⟨φ,hφc⟩
  have hm := RealRMK.rieszMeasure_le_of_eq_one
    (limitPositive (fun n => densityPositive (hw n) (h0 n))
      (fun n ψ => densityPositive_norm_bound (hw n) (h0 n) (hb n) ψ))
    (f := φ') (fun x => (hφ x).1) hK hφ1
  have he : limitPositive (fun n => densityPositive (hw n) (h0 n))
      (fun n ψ => densityPositive_norm_bound (hw n) (h0 n) (hb n) ψ) φ' ≤ D := by
    apply le_of_tendsto (limit_tendsto (fun n => densityPositive (hw n) (h0 n))
      (fun n ψ => densityPositive_norm_bound (hw n) (h0 n) (hb n) ψ) φ')
    filter_upwards [Nat.hyperfilter_le_atTop hD] with n hn
    exact (density_test_le_set (hw n) (h0 n) φ' hO.measurableSet hφs (fun x => (hφ x).2)).trans hn
  exact hm.trans (ENNReal.ofReal_le_ofReal he)
end WeakCompact

namespace WeakCompact
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {μ : Measure X}
variable (w : ℕ → X → ℝ) (hw : ∀ n, Integrable (w n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0≤w n x)
  {B : ℝ} (hb : ∀ n, (∫ x,w n x ∂μ) ≤ B)

lemma densityLimit_sharp_mass {D : ℝ} {a : ℕ → ℝ}
    (ha : ∀ n, (∫ x,w n x ∂μ) ≤ a n) (ht : Tendsto a atTop (𝓝 D)) :
    densityLimit w hw h0 hb Set.univ ≤ ENNReal.ofReal D := by
  have := densityLimit_regular w hw h0 hb
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  apply iSup_le
  intro K
  apply iSup_le
  intro _
  apply iSup_le
  intro hK
  have he (ε : ℝ) (hε : 0<ε) : densityLimit w hw h0 hb K ≤ ENNReal.ofReal (D+ε) := by
    apply densityLimit_compact_bound w hw h0 hb hK isOpen_univ (subset_univ K)
    filter_upwards [ht.eventually (gt_mem_nhds (by linarith : D<D+ε))] with n hn
    simpa only [Measure.restrict_univ] using (ha n).trans hn.le
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := densityLimit w hw h0 hb K))
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (show Tendsto (fun n : ℕ => D+1/((n:ℝ)+1)) atTop (𝓝 D) by
        simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  exact Eventually.of_forall (fun n => he _ (by positivity))

omit [T2Space X] [BorelSpace X] [LocallyCompactSpace X] in
lemma absolutelyContinuous_of_compact_null {ν : Measure X} [ν.InnerRegular]
    (h : ∀ K : Set X, IsCompact K → μ K=0 → ν K=0) : ν ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hμ
  rw [hs.measure_eq_iSup_isCompact]
  apply le_antisymm _ bot_le
  apply iSup_le
  intro K
  apply iSup_le
  intro hKs
  apply iSup_le
  intro hK
  exact (h K hK (measure_mono_null hKs hμ)).le
end WeakCompact

namespace SobolevBand
open DiskMoments DiskMaximalTools

lemma low_pos (n : ℕ) : 0<low n := by unfold low; positivity
lemma low_le_high (n : ℕ) : low n ≤ high n := by
  have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
  unfold low high
  have hi : ((2:ℝ)^n)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hp
  linarith
lemma low_antitone : Antitone low := by
  intro n m hnm
  exact inv_anti₀ (by positivity : (0:ℝ)<2^n) (pow_le_pow_right₀ (by norm_num) hnm)
lemma high_monotone : Monotone high := by
  intro n m hnm
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hnm) (by norm_num)
lemma low_tendsto : Tendsto low atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((2:ℝ)^n)⁻¹) atTop (𝓝 0)
  simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2⁻¹:ℝ)<1)
lemma high_tendsto : Tendsto high atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop (by norm_num)
lemma eventually_mem_band {r : ℝ} (hr : 0<r) : ∀ᶠ n in atTop, r∈Icc (low n) (high n) := by
  filter_upwards [low_tendsto.eventually (gt_mem_nhds hr),high_tendsto.eventually (eventually_ge_atTop r)] with n hn hn'
  exact ⟨hn.le,hn'⟩

lemma absolute_average_eq {f : ℂ → ℝ} (hf : Integrable f) (x : ℂ) {r : ℝ} (hr : 0<r) :
    absoluteMeasure f (Metric.ball x r)/volume (Metric.ball x r) =
      ENNReal.ofReal (signedAverage (fun y => |f y|) x r) := by
  rw [absoluteMeasure,withDensity_apply _ measurableSet_ball,volume_disk_real x hr.le,signedAverage,
    ENNReal.ofReal_div_of_pos (mul_pos Real.pi_pos (sq_pos_of_pos hr)),
    ofReal_integral_eq_lintegral_ofReal hf.abs.integrableOn (ae_of_all _ (fun y => abs_nonneg (f y)))]

lemma abs_average_nonneg (f : ℂ → ℝ) (x : ℂ) {r : ℝ} (hr : 0<r) :
    0 ≤ signedAverage (fun y => |f y|) x r := by
  unfold signedAverage
  exact div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (by positivity)

lemma abs_band_nonneg {f : ℂ → ℝ} (hf : Integrable f) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) (x : ℂ) : 0 ≤ band (fun y => |f y|) a b x :=
  (abs_average_nonneg f x ha).trans (average_le_band hf.abs ha ⟨le_rfl,hab⟩ x)

lemma abs_band_le_maximal {f : ℂ → ℝ} (hf : Integrable f) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) {x : ℂ} (hx : maximalComplex f x ≠ ⊤) :
    band (fun y => |f y|) a b x ≤ maximalComplexReal f x := by
  apply band_le hab x
  intro r hr
  apply (ENNReal.ofReal_le_iff_le_toReal hx).mp
  rw [← absolute_average_eq hf x (ha.trans_le hr.1)]
  exact disk_average_le_rationalMaximal_exact _ x (ha.trans_le hr.1)

lemma band_mono_interval {f : ℂ → ℝ} (hf : Integrable f) {a b c d : ℝ}
    (ha : 0<a) (hac : a≤c) (hcd : c≤d) (hdb : d≤b) (x : ℂ) :
    band f c d x ≤ band f a b x := by
  apply band_le hcd x
  intro r hr
  exact average_le_band hf ha ⟨hac.trans hr.1,hr.2.trans hdb⟩ x

lemma diagonal_monotone {f : ℂ → ℝ} (hf : Integrable f) (x : ℂ) :
    Monotone (fun n => band f (low n) (high n) x) := by
  intro n m hnm
  exact band_mono_interval hf (low_pos m) (low_antitone hnm) (low_le_high n) (high_monotone hnm) x

lemma diagonal_tendsto {f : ℂ → ℝ} (hf : Integrable f) {x : ℂ} (hx : maximalComplex f x≠⊤) :
    Tendsto (fun n => band (fun y => |f y|) (low n) (high n) x) atTop (𝓝 (maximalComplexReal f x)) := by
  let v := fun n => band (fun y => |f y|) (low n) (high n) x
  have hb : BddAbove (range v) := ⟨maximalComplexReal f x,by
    rintro _ ⟨n,rfl⟩; exact abs_band_le_maximal hf (low_pos n) (low_le_high n) hx⟩
  have hs0 : 0≤⨆ n,v n := (abs_band_nonneg hf (low_pos 0) (low_le_high 0) x).trans (le_ciSup hb 0)
  have hs : (⨆ n,v n) = maximalComplexReal f x := by
    apply le_antisymm
    · apply ciSup_le
      intro n
      exact abs_band_le_maximal hf (low_pos n) (low_le_high n) hx
    · have he : maximalComplex f x ≤ ENNReal.ofReal (⨆ n,v n) := by
        rw [maximalComplex_eq_all_radii]
        apply iSup_le
        intro r
        apply iSup_le
        intro hr
        obtain ⟨n,hn⟩ := (eventually_mem_band hr).exists
        rw [absolute_average_eq hf x hr]
        exact ENNReal.ofReal_le_ofReal ((average_le_band hf.abs (low_pos n) hn x).trans (le_ciSup hb n))
      simpa only [maximalComplexReal,ENNReal.toReal_ofReal hs0] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  rw [← hs]
  exact tendsto_atTop_ciSup (diagonal_monotone hf.abs x) hb

lemma locallyIntegrable_maximal {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hw : WeakSobolev.HasGradient (μ := volume) f g) :
    LocallyIntegrable (maximalComplexReal f) :=
  (memLp_maximalComplexReal hf (WeakSobolev.memLp_two Complex.finrank_real_complex hf hg hw)).locallyIntegrable (by norm_num)

lemma diagonal_local_L1 {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hw : WeakSobolev.HasGradient (μ := volume) f g)
    {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => ∫ x in K, ‖band (fun y => |f y|) (low n) (high n) x-maximalComplexReal f x‖) atTop (𝓝 0) := by
  let _ := absoluteMeasure_finite hf
  have hg' := (WeakSobolev.abs_gradient_bound hf hg).1
  have hw' := hw.abs hf hg
  have hL n := band_lipschitz hf.abs hg' hw' (low_pos n) (low_le_high n)
  have hM := locallyIntegrable_maximal hf hg hw
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ : ℂ => (0:ℝ))
    (fun x => 2*maximalComplexReal f x)
    (fun n => (((hL n).continuous.aestronglyMeasurable).sub ((measurable_rationalMaximal (absoluteMeasure f)).ennreal_toReal.aestronglyMeasurable)).norm.restrict)
    ((hM.integrableOn_isCompact hK).const_mul 2)
    (fun n => ?_) (?_)
  · simpa only [integral_zero,Pi.sub_apply,maximalComplexReal,maximalComplex] using ht
  · filter_upwards [ae_restrict_of_ae (maximalComplex_ae_finite hf)] with x hx
    have h0 := abs_band_nonneg hf (low_pos n) (low_le_high n) x
    have h1 := abs_band_le_maximal hf (low_pos n) (low_le_high n) hx
    change ‖‖band (fun y => |f y|) (low n) (high n) x-maximalComplexReal f x‖‖ ≤ _
    rw [Real.norm_of_nonneg (norm_nonneg _),Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr h1)]
    have h2 : 0 ≤ maximalComplexReal f x := ENNReal.toReal_nonneg
    linarith
  · filter_upwards [ae_restrict_of_ae (maximalComplex_ae_finite hf)] with x hx
    simpa only [sub_self,norm_zero,Pi.sub_apply,maximalComplexReal,maximalComplex] using ((diagonal_tendsto hf hx).sub (tendsto_const_nhds (x := maximalComplexReal f x))).norm
end SobolevBand

namespace SobolevBand
open DiskMoments RadiusEnvelope SignedRuns GeometricFilter DyadicHats ActualLabels

lemma smooth_band_integrable_gradient {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    Integrable (gradient (band f a b)) :=
  _root_.OAI.LipschitzWith.integrable_gradient (smooth_band_lipschitz hf hc ha hab) (run_envelope_hasCompactSupport hf hc ha hab)

lemma band_ae_touching {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    ∀ᵐ x, ∀ r ∈ Icc a b, band f a b x=signedAverage f x r →
      gradient (band f a b) x=gradient (fun y => signedAverage f y r) x := by
  obtain ⟨L,hL⟩ := hf.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  filter_upwards [(smooth_band_lipschitz hf hc ha hab).ae_differentiableAt] with x hx
  intro r hr he
  have hd := (hasFDerivAt_signedAverage hf (fun y => norm_fderiv_le_of_lipschitz ℝ hL (x₀ := y)) x (ha.trans_le hr.1)).differentiableAt
  exact congrArg (InnerProductSpace.toDual ℝ ℂ).symm
    (fderiv_touching hr (fun y => signedAverage_radius_continuousOn hf y ha) he hx hd)

/-- Quantitative large-radius truncation; small radii are the only term needing
localization. Differentiable touching avoids any unproved max-chain rule. -/
lemma split_gradient {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {a t b : ℝ} (ha : 0<a) (hat : a≤t) (htb : t≤b) :
    ∀ᵐ x, ‖gradient (band f a b) x‖ ≤ ‖gradient (band f a t) x‖+
      (∫ y,‖gradient f y‖)/(Real.pi*t^2) := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  filter_upwards [band_ae_touching hf hc ha (hat.trans htb),band_ae_touching hf hc ha hat] with x hx hx'
  obtain ⟨r,hr,he,hm⟩ := attains (u := fun r x => signedAverage f x r) (hat.trans htb) x (signedAverage_radius_continuousOn hf x ha)
  have htouch := hx r hr he
  by_cases hrt : r≤t
  · have hs : band f a t x=signedAverage f x r := by
      apply le_antisymm
      · apply band_le hat x
        intro s hs
        exact hm s ⟨hs.1,hs.2.trans htb⟩
      · exact average_le_band hfi ha ⟨hr.1,hrt⟩ x
    rw [htouch,← hx' r ⟨hr.1,hrt⟩ hs]
    exact le_add_of_nonneg_right (by positivity)
  · rw [htouch]
    have hnorm := norm_fderiv_le_of_lipschitz ℝ (smooth_average_lipschitz hf hc (ha.trans_le hat) (le_of_not_ge hrt)) (x₀ := x)
    rw [← WeakSobolev.norm_gradient_fderiv] at hnorm
    exact hnorm.trans (le_add_of_nonneg_left (norm_nonneg _))
end SobolevBand

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Localization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace NullLocalization
open PlanePotential DiskMoments

lemma unitRegion_compact : IsCompact unitRegion := by
  simpa only [unitRegion,Metric.closedBall,dist_zero_right] using isCompact_closedBall (0:ℂ) 8
lemma unitRegion_measurable : MeasurableSet unitRegion := unitRegion_compact.measurableSet
lemma unitRegion_finite : volume unitRegion < ⊤ := unitRegion_compact.measure_lt_top

/-- A fixed-radius Poincare inequality derived from the proved Green kernel,
not added as a Sobolev axiom. The subsequent cutoff is one on the radius-four disk. -/
lemma unit_poincare : ∃ P : ℝ, 0 ≤ P ∧ ∀ {g : ℂ → ℝ},
    ContDiff ℝ 1 g → HasCompactSupport g → ∃ c : ℝ,
    (∫ x in unitRegion, ‖g x-c‖) ≤ P*(∫ x in unitRegion, ‖gradient g x‖) := by
  obtain ⟨ψ,B,L,hB,hL,hψ,hψc,hψ1,hψs,hψB,hψL⟩ := exists_kernel_cutoff
  let A : ℝ≥0∞ := ENNReal.ofReal ((2*B*(1+8)^2)^(3/2:ℝ)*(4*Real.pi*(32:ℝ)^(1/2:ℝ)))
  let Z : ℝ≥0∞ := A^(2/3:ℝ)*(volume unitRegion)^(1/3:ℝ)
  have hZ : Z ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) unitRegion_finite.ne)
  refine ⟨Z.toReal,ENNReal.toReal_nonneg,?_⟩
  intro g hg hc
  let c := ∫ z,ψ z*g z
  refine ⟨c,?_⟩
  let β := unitRegion.indicator (gradient g)
  have hgi : Integrable (gradient g) := (continuous_gradient hg).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)
  have hβ : Integrable β := hgi.indicator unitRegion_measurable
  have hβs : ∀ y, β y≠0 → ‖y‖ ≤ 8 := by
    intro y hy
    by_contra hh
    change y∉unitRegion at hh
    exact hy (indicator_of_notMem hh _)
  have hβv : (∫ y,‖β y‖) = ∫ y in unitRegion,‖gradient g y‖ := by
    rw [← integral_indicator unitRegion_measurable]
    congr 1
    ext y
    exact norm_indicator_eq_indicator_norm _ _
  obtain ⟨D,hD⟩ := hg.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  have hp := green_root_lp hψ.continuous.measurable hψs hψB
    (by norm_num : (0:ℝ)<1+8) hB (by norm_num : (0:ℝ)<8+8) hβ hβs
  have hex : (fun x => ∫ y,inner ℝ (green ψ x y) (β y)) =ᵐ[volume.restrict unitRegion] (fun x => g x-c) := by
    filter_upwards [ae_restrict_mem unitRegion_measurable] with x hx
    calc
      _ = ∫ y,inner ℝ (green ψ x y) (gradient g y) := by
        apply integral_congr_ae
        exact ae_of_all _ (green_restrict_density hψs (by norm_num : (1:ℝ)≤8) _ hx)
      _ = _ := green_gradient_representation hψ.continuous hψc hg
        (fun y => norm_fderiv_le_of_lipschitz ℝ hD (x₀ := y)) hψ1 x
  have hs : eLpNorm (fun x => g x-c) (3/2) (volume.restrict unitRegion) ≤
      A^(2/3:ℝ)*ENNReal.ofReal (∫ y in unitRegion,‖gradient g y‖) := by
    rw [← eLpNorm_congr_ae hex,← hβv]
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
      (ENNReal.div_ne_top (by norm_num) (by norm_num))]
    convert eLpNorm_three_halves_bound _ hp using 1 <;> norm_num [A,unitRegion]
  have hl := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := fun x => g x-c) (μ := volume.restrict unitRegion)
    (show (1:ℝ≥0∞)≤3/2 by rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]; norm_num) (hg.continuous.sub continuous_const).aestronglyMeasurable
  have he : eLpNorm (fun x => g x-c) 1 (volume.restrict unitRegion) ≤
      Z*ENNReal.ofReal (∫ y in unitRegion,‖gradient g y‖) := by
    apply hl.trans
    have hexp : 1/(1:ℝ≥0∞).toReal-1/(3/2:ℝ≥0∞).toReal=(1/3:ℝ) := by norm_num
    rw [hexp,Measure.restrict_apply_univ]
    have hh := mul_le_mul_right hs ((volume unitRegion)^(1/3:ℝ))
    simpa only [Z,mul_assoc,mul_left_comm,mul_comm] using hh
  have hin : IntegrableOn (fun x => g x-c) unitRegion :=
    (hg.continuous.sub continuous_const).continuousOn.integrableOn_compact unitRegion_compact
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hin] at he
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top hZ ENNReal.ofReal_ne_top) he
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg _))] using ht
end NullLocalization

namespace NullLocalization
open DiskMoments WeakSobolev

lemma unit_localization : ∃ D : ℝ, 0≤D ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∃ (h : ℂ → ℝ) (c : ℝ), ContDiff ℝ 1 h ∧ HasCompactSupport h ∧
    (∀ x, ‖x‖≤4 → h x=g x-c) ∧
    (∫ x,‖gradient h x‖) ≤ D*(∫ x in unitRegion,‖gradient g x‖) := by
  obtain ⟨P,hP,hpoi⟩ := unit_poincare
  obtain ⟨L,hL⟩ := (unitCutoff.contDiff (n := (1:ℕ∞))).lipschitzWith_of_hasCompactSupport unitCutoff.hasCompactSupport one_ne_zero
  refine ⟨1+L*P,by positivity,?_⟩
  intro g hg hc
  obtain ⟨c,hc'⟩ := hpoi hg hc
  let h := fun x => unitCutoff x*(g x-c)
  have hd : ContDiff ℝ 1 h := unitCutoff.contDiff.mul (hg.sub contDiff_const)
  have hs : HasCompactSupport h := unitCutoff.hasCompactSupport.mul_right
  refine ⟨h,c,hd,hs,?_,?_⟩
  · intro x hx
    have he : unitCutoff x=1 := unitCutoff.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,unitCutoff] using hx)
    simp only [h,he,one_mul]
  · have hi : Integrable (gradient h) := (continuous_gradient hd).integrable_of_hasCompactSupport (gradient_hasCompactSupport hs)
    have his : Function.support (fun x => ‖gradient h x‖) ⊆ unitRegion := by
      intro x hx
      have ht : x∈tsupport h := support_fderiv_subset ℝ (by
        intro he
        apply hx
        change ‖gradient h x‖=0
        rw [norm_gradient_fderiv,he,norm_zero])
      have hh : tsupport h ⊆ tsupport (unitCutoff : ℂ → ℝ) := tsupport_mul_subset_left
      have hx' := hh ht
      rw [unitCutoff.tsupport_eq] at hx'
      change ‖x‖≤8
      simpa only [Metric.mem_closedBall,dist_zero_right,unitCutoff] using hx'
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => Function.notMem_support.mp (fun hh => hx (his hh)))]
    have hig : IntegrableOn (fun x => ‖gradient g x‖) unitRegion :=
      ((continuous_gradient hg).norm).continuousOn.integrableOn_compact unitRegion_compact
    have hid : IntegrableOn (fun x => ‖g x-c‖) unitRegion :=
      (hg.continuous.sub continuous_const).norm.continuousOn.integrableOn_compact unitRegion_compact
    have hb (x : ℂ) : ‖gradient h x‖ ≤ ‖gradient g x‖+L*‖g x-c‖ := by
      rw [norm_gradient_fderiv]
      have he := fderiv_mul ((unitCutoff.contDiff (n := (1:ℕ∞))).differentiable one_ne_zero x)
        ((hg.differentiable one_ne_zero x).sub_const c)
      change fderiv ℝ h x = _ at he
      rw [he]
      have hχ : ‖unitCutoff x‖≤1 := by rw [Real.norm_of_nonneg unitCutoff.nonneg]; exact unitCutoff.le_one
      have hχd := norm_fderiv_le_of_lipschitz ℝ hL (x₀ := x)
      calc
        _ ≤ ‖unitCutoff x • fderiv ℝ (fun x => g x-c) x‖+‖(g x-c) • fderiv ℝ (unitCutoff : ℂ → ℝ) x‖ := norm_add_le _ _
        _ ≤ 1*‖fderiv ℝ g x‖+‖g x-c‖*L := by
          rw [norm_smul,norm_smul,fderiv_sub_const]
          exact add_le_add (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)) (mul_le_mul_of_nonneg_left hχd (norm_nonneg _))
        _ = _ := by rw [one_mul,← norm_gradient_fderiv]; ring
    have hm := integral_mono hi.norm.integrableOn (hig.add (hid.const_mul (L:ℝ))) hb
    simp only [Pi.add_apply] at hm
    rw [integral_add hig (hid.const_mul (L:ℝ)),integral_const_mul] at hm
    nlinarith [mul_le_mul_of_nonneg_left hc' L.coe_nonneg]
end NullLocalization

namespace NullLocalization
open DiskMoments PhysicalCells WeakSobolev

lemma region_measurable (p : ℂ) (t : ℝ) : MeasurableSet (region p t) :=
  measurableSet_le (continuous_norm.comp (continuous_id.sub continuous_const)).measurable measurable_const

lemma integral_stretch (F : ℂ → ℝ) (p : ℂ) (t : ℝ) :
    (∫ x,F (p+t • x)) = (t^2)⁻¹*(∫ x,F x) := by
  have h := Measure.integral_comp_smul volume (fun x : ℂ => F (p+x)) t
  simpa only [Complex.finrank_real_complex,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),smul_eq_mul,
    integral_add_left_eq_self] using h

lemma norm_toUnit (p x : ℂ) {t : ℝ} (ht : 0<t) : ‖toUnit p t x‖=‖x-p‖/t := by
  simp only [toUnit,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),div_eq_mul_inv,mul_comm]

lemma comp_stretch_compact {g : ℂ → ℝ} (hc : HasCompactSupport g) (p : ℂ) {t : ℝ} (ht : t≠0) :
    HasCompactSupport (fun x => g (p+t • x)) := by
  exact hc.comp_homeomorph ((Homeomorph.smulOfNeZero t ht).trans (Homeomorph.addLeft p))

lemma comp_toUnit_compact {g : ℂ → ℝ} (hc : HasCompactSupport g) (p : ℂ) {t : ℝ} (ht : t≠0) :
    HasCompactSupport (fun x => g (toUnit p t x)) := by
  exact hc.comp_homeomorph ((Homeomorph.subRight p).trans (Homeomorph.smulOfNeZero t⁻¹ (inv_ne_zero ht)))

lemma gradient_toUnit {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p x : ℂ) (t : ℝ) :
    gradient (fun y => g (toUnit p t y)) x=t⁻¹ • gradient g (toUnit p t x) := by
  have he : (fun y => g (toUnit p t y)) = (fun y => g (-(t⁻¹ • p)+t⁻¹ • y)) := by
    ext y; congr 1; simp only [toUnit,smul_sub]; abel
  rw [he,AffineDensities.gradient_affine hg]
  change t⁻¹ • gradient g (-(t⁻¹ • p)+t⁻¹ • x)=_
  congr 2
  simp only [toUnit,smul_sub]; abel

lemma integral_gradient_toUnit {g : ℂ → ℝ} (hg : Differentiable ℝ g) (p : ℂ) {t : ℝ} (ht : 0<t) :
    (∫ x,‖gradient (fun y => g (toUnit p t y)) x‖)=t*(∫ x,‖gradient g x‖) := by
  simp_rw [gradient_toUnit hg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
  rw [integral_const_mul]
  have he : (∫ x, ‖gradient g (toUnit p t x)‖) = t^2*(∫ x,‖gradient g x‖) := by
    rw [show (fun x => ‖gradient g (toUnit p t x)‖) =
      (fun x => ‖gradient g (-(t⁻¹ • p)+t⁻¹ • x)‖) by ext x; congr 2; simp only [toUnit,smul_sub]; abel]
    rw [integral_stretch (fun z => ‖gradient g z‖) (-(t⁻¹ • p)) t⁻¹,inv_pow,inv_inv]
  rw [he]
  field_simp

lemma local_integral_gradient_stretch {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (p : ℂ) {t : ℝ} (ht : 0<t) :
    (∫ x in unitRegion,‖gradient (fun y => g (p+t • y)) x‖)=
      t⁻¹*(∫ x in region p t,‖gradient g x‖) := by
  simp_rw [AffineDensities.gradient_affine hg,AffineDensities.rescale,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht]
  rw [integral_const_mul,← integral_indicator unitRegion_measurable,
    ← integral_indicator (region_measurable p t)]
  have he : unitRegion.indicator (fun x => ‖gradient g (p+t • x)‖) =
      (fun x => (region p t).indicator (fun z => ‖gradient g z‖) (p+t • x)) := by
    ext x
    have hx : p+t • x∈region p t ↔ x∈unitRegion := by
      change ‖p+t • x-p‖≤8*t ↔ ‖x‖≤8
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      constructor <;> intro hh <;> nlinarith
    by_cases h : x∈unitRegion
    · rw [Set.indicator_of_mem h,Set.indicator_of_mem (hx.mpr h)]
    · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem (fun hh => h (hx.mp hh))]
  rw [he,integral_stretch]
  field_simp

lemma physical_localization : ∃ D : ℝ, 0≤D ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∀ (p : ℂ) {t : ℝ}, 0<t →
    ∃ (h : ℂ → ℝ) (c : ℝ), ContDiff ℝ 1 h ∧ HasCompactSupport h ∧
      (∀ x, ‖x-p‖≤4*t → h x=g x-c) ∧
      (∫ x,‖gradient h x‖) ≤ D*(∫ x in region p t,‖gradient g x‖) := by
  obtain ⟨D,hD,he⟩ := unit_localization
  refine ⟨D,hD,?_⟩
  intro g hg hc p t ht
  let G := fun x => g (p+t • x)
  have ha : ContDiff ℝ 1 (fun x : ℂ => p+t • x) := contDiff_const.add (contDiff_id.const_smul t)
  have hG : ContDiff ℝ 1 G := hg.comp ha
  have hmap : ContDiff ℝ 1 (toUnit p t) := (contDiff_id.sub contDiff_const).const_smul t⁻¹
  obtain ⟨h,c,hd,hs,hh,hb⟩ := he hG (comp_stretch_compact hc p ht.ne')
  refine ⟨fun x => h (toUnit p t x),c,hd.comp hmap,
    comp_toUnit_compact hs p ht.ne',?_,?_⟩
  · intro x hx
    have hx' : ‖toUnit p t x‖≤4 := by rw [norm_toUnit p x ht]; exact (div_le_iff₀ ht).mpr hx
    simpa only [G,affine_toUnit p ht.ne'] using hh _ hx'
  · rw [integral_gradient_toUnit (hd.differentiable one_ne_zero) p ht]
    have he' := mul_le_mul_of_nonneg_left hb ht.le
    rw [local_integral_gradient_stretch (hg.differentiable one_ne_zero) p ht] at he'
    convert he' using 1 <;> first | rfl | field_simp
end NullLocalization

namespace NullLocalization
open SobolevBand DiskMoments PhysicalCells DyadicHats RadiusEnvelope

lemma band_sub_local {g h : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {a t : ℝ}
    (ha : 0<a) (hat : a≤t) {p x : ℂ} {c : ℝ}
    (hlocal : ∀ y, ‖y-p‖≤4*t → h y=g y-c) (hx : ‖x-p‖<3*t) :
    band h a t x=band g a t x-c := by
  have hav (r : ℝ) (hr : r∈Icc a t) : signedAverage h x r=signedAverage g x r-c := by
    rw [← signedAverage_sub_const hg.continuous c x (ha.trans_le hr.1)]
    unfold signedAverage
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    apply hlocal
    have hn := norm_add_le (y-x) (x-p)
    rw [sub_add_sub_cancel] at hn
    have hd : ‖y-x‖<r := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
    linarith [hr.2]
  have hi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hi' : Integrable h := hh.continuous.integrable_of_hasCompactSupport hhc
  apply le_antisymm
  · apply band_le hat x
    intro r hr
    rw [hav r hr]
    exact sub_le_sub_right (average_le_band hi ha hr x) c
  · obtain ⟨r,hr,he,_⟩ := attains (u := fun r x => signedAverage g x r) hat x (signedAverage_radius_continuousOn hg x ha)
    rw [show band g a t x=signedAverage g x r from he,← hav r hr]
    exact average_le_band hi' ha hr x

lemma gradient_band_local {g h : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) {a t : ℝ}
    (ha : 0<a) (hat : a≤t) {p x : ℂ} {c : ℝ}
    (hlocal : ∀ y, ‖y-p‖≤4*t → h y=g y-c) (hx : ‖x-p‖≤2*t) :
    gradient (band h a t) x=gradient (band g a t) x := by
  have ht : 0<t := ha.trans_le hat
  have he : band h a t =ᶠ[𝓝 x] (fun y => band g a t y-c) := by
    have hn : ‖x-p‖<3*t := by linarith
    filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds hn] with y hy
    exact band_sub_local hg hh hgc hhc ha hat hlocal hy
  apply congrArg (InnerProductSpace.toDual ℝ ℂ).symm
  exact he.fderiv_eq.trans (fderiv_sub_const c)

lemma mem_cell_norm {t : ℝ} (ht : 0<t) {p x : ℂ} (hx : x∈cell p t) : ‖x-p‖≤2*t := by
  have hn := norm_unitCell hx
  change ‖toUnit p t x‖≤2 at hn
  rw [norm_toUnit p x ht] at hn
  exact (div_le_iff₀ ht).mp hn

lemma smooth_local_band : ∃ C : ℝ, 0<C ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∀ {a : ℝ}, 0<a → ∀ m : ℕ, ∀ p : ℂ,
    (∫ x in cell p (2*((2:ℝ)^m*a)), ‖gradient (band g a (2*((2:ℝ)^m*a))) x‖) ≤
      C*(∫ x in region p (2*((2:ℝ)^m*a)), ‖gradient g x‖) := by
  obtain ⟨C,hC,hbound⟩ := smooth_dyadic_bound
  obtain ⟨D,hD,hloc⟩ := physical_localization
  refine ⟨C*(D+1),by positivity,?_⟩
  intro g hg hc a ha m p
  let t := 2*((2:ℝ)^m*a)
  have ht : 0<t := by dsimp only [t]; positivity
  have hat : a≤t := by
    have hp : (1:ℝ)≤2^m := one_le_pow₀ (by norm_num)
    dsimp only [t]; nlinarith
  obtain ⟨h,c,hd,hs,hh,hb⟩ := hloc hg hc p ht
  have hbi := smooth_band_integrable_gradient hd hs ha hat
  calc
    _ = ∫ x in cell p t,‖gradient (band h a t) x‖ := by
      apply setIntegral_congr_fun (cell_measurable p t)
      intro x hx
      change ‖gradient (band g a t) x‖=‖gradient (band h a t) x‖
      rw [gradient_band_local hg hd hc hs ha hat hh (mem_cell_norm ht hx)]
    _ ≤ ∫ x, ‖gradient (band h a t) x‖ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => norm_nonneg _)) hbi.norm
    _ ≤ C*(∫ x,‖gradient h x‖) := hbound hd hs ha m
    _ ≤ C*(D*(∫ x in region p t,‖gradient g x‖)) := mul_le_mul_of_nonneg_left hb hC.le
    _ ≤ C*(D+1)*(∫ x in region p t,‖gradient g x‖) := by
      have h0 : 0 ≤ (∫ x in region p t, ‖gradient g x‖) := integral_nonneg (fun x => norm_nonneg (gradient g x))
      nlinarith
end NullLocalization

namespace NullLocalization
open scoped Classical
open PhysicalCells DyadicHats DirectionNeighbors Finset

lemma region_indices {t : ℝ} (ht : 0<t) (y : ℂ) {p : ℤ×ℤ}
    (hp : y∈region (point t p) t) : p∈window 10 (gridIndex t y) := by
  apply (mem_window_iff ht 10 _ _).mpr
  have hn := mem_cell_norm ht (mem_index_cell ht y)
  have hd := norm_add_le (point t p-y) (y-point t (gridIndex t y))
  rw [sub_add_sub_cancel,norm_sub_rev (point t p) y] at hd
  change ‖y-point t p‖≤8*t at hp
  exact (boxNorm_le_norm _).trans (by norm_num; linarith)

lemma regions_overlap {t : ℝ} (ht : 0<t) (S : Finset (ℤ×ℤ)) (y : ℂ) :
    (∑ p∈S, if y∈region (point t p) t then (1:ℝ) else 0) ≤ 441 := by
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hs : S.filter (fun p => y∈region (point t p) t) ⊆ window 10 (gridIndex t y) := by
    intro p hp; exact region_indices ht y (Finset.mem_filter.mp hp).2
  have h := Finset.card_le_card hs
  rw [card_window] at h
  exact_mod_cast h

lemma usedRegion_measurable (O : Set ℂ) (t : ℝ) (p : ℤ×ℤ) : MeasurableSet (usedRegion O t p) := by
  unfold usedRegion
  split_ifs
  · exact region_measurable _ _
  · exact MeasurableSet.empty

lemma usedRegion_subset {O K : Set ℂ} {t : ℝ} (ht : 0<t)
    (hO : O⊆Metric.thickening t K) (p : ℤ×ℤ) : usedRegion O t p ⊆ Metric.thickening (12*t) K := by
  intro y hy
  unfold usedRegion at hy
  split_ifs at hy with hp
  · obtain ⟨z,hzO,hzcell⟩ := hp
    obtain ⟨w,hw,hzw⟩ := Metric.mem_thickening_iff.mp (hO hzO)
    apply Metric.mem_thickening_iff.mpr
    refine ⟨w,hw,?_⟩
    have hz := mem_cell_norm ht hzcell
    change ‖y-point t p‖≤8*t at hy
    have h1 := dist_triangle y (point t p) z
    have h2 := dist_triangle y z w
    simp only [dist_eq_norm] at h1 h2 hzw ⊢
    rw [norm_sub_rev (point t p) z] at h1
    linarith
  · exact hy.elim

lemma usedRegion_budget {O K : Set ℂ} {t : ℝ} (ht : 0<t)
    (hO : O⊆Metric.thickening t K) {F : ℂ → ℝ} (hF : Integrable F) (h0 : ∀ y,0≤F y)
    (S : Finset (ℤ×ℤ)) :
    (∑ p∈S,∫ y in usedRegion O t p,F y) ≤ 441*(∫ y in Metric.thickening (12*t) K,F y) := by
  classical
  let T := Metric.thickening (12*t) K
  have hT : MeasurableSet T := Metric.isOpen_thickening.measurableSet
  have hi (p : ℤ×ℤ) : Integrable ((usedRegion O t p).indicator F) := hF.indicator (usedRegion_measurable _ _ _)
  simp_rw [← integral_indicator (usedRegion_measurable O t _)]
  rw [← integral_finsetSum S (fun p _ => hi p),← integral_indicator hT,← integral_const_mul]
  apply integral_mono (integrable_finsetSum S (fun p _ => hi p)) ((hF.indicator hT).const_mul 441)
  intro y
  dsimp only
  by_cases hy : y∈T
  · rw [Set.indicator_of_mem hy]
    calc
      _ ≤ ∑ p∈S,(if y∈region (point t p) t then (1:ℝ) else 0)*F y := by
        apply Finset.sum_le_sum
        intro p _
        unfold usedRegion
        by_cases hp : touches O t p
        · simp only [ite_eq_left hp,Set.indicator_apply]
          split_ifs <;> simp
        · simp only [ite_eq_right hp,Set.indicator_empty]
          split_ifs
          · simpa using h0 y
          · simp
      _ = (∑ p∈S,if y∈region (point t p) t then (1:ℝ) else 0)*F y := (Finset.sum_mul _ _ _).symm
      _ ≤ 441*F y := mul_le_mul_of_nonneg_right (regions_overlap ht S y) (h0 y)
  · rw [Set.indicator_of_notMem hy,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro p _
    exact Set.indicator_of_notMem (fun hp => hy (usedRegion_subset ht hO p hp)) F
end NullLocalization

namespace NullLocalization
open SobolevBand DiskMoments PhysicalCells DyadicHats

lemma smooth_small_local_budget : ∃ C : ℝ, 0<C ∧ ∀ {g : ℂ → ℝ}, ContDiff ℝ 1 g →
    HasCompactSupport g → ∀ {a : ℝ}, 0<a → ∀ m : ℕ, ∀ {O K : Set ℂ}, MeasurableSet O →
    O⊆Metric.thickening (2*((2:ℝ)^m*a)) K →
    (∫ x in O,‖gradient (band g a (2*((2:ℝ)^m*a))) x‖) ≤
      C*(∫ x in Metric.thickening (12*(2*((2:ℝ)^m*a))) K,‖gradient g x‖) := by
  classical
  obtain ⟨C,hC,hlocal⟩ := smooth_local_band
  refine ⟨C*441,by positivity,?_⟩
  intro g hg hc a ha m O K hO hOK
  let t := 2*((2:ℝ)^m*a)
  have ht : 0<t := by dsimp only [t]; positivity
  have hat : a≤t := by
    have hpow : (1:ℝ)≤2^m := one_le_pow₀ (by norm_num)
    dsimp only [t]; nlinarith
  let F := fun x => ‖gradient (band g a t) x‖
  let G := fun x => ‖gradient g x‖
  have hF : Integrable F := (smooth_band_integrable_gradient hg hc ha hat).norm
  have hG : Integrable G := ((continuous_gradient hg).integrable_of_hasCompactSupport (gradient_hasCompactSupport hc)).norm
  have hF0 x : 0≤F x := norm_nonneg _
  have hG0 x : 0≤G x := norm_nonneg _
  have hi : Integrable (O.indicator F) := hF.indicator hO
  have hi0 x : 0≤O.indicator F x := Set.indicator_nonneg (fun x _ => hF0 x) x
  let B := fun p : ℤ×ℤ => C*(∫ x in usedRegion O t p,G x)
  have hB p : 0≤B p := mul_nonneg hC.le (integral_nonneg hG0)
  have hcell p : (∫⁻ x in cell (point t p) t, ENNReal.ofReal (O.indicator F x)) ≤ ENNReal.ofReal (B p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ hi0)]
    apply ENNReal.ofReal_le_ofReal
    by_cases hp : touches O t p
    · change _ ≤ C*(∫ x in usedRegion O t p,G x)
      rw [usedRegion,ite_eq_left hp]
      apply (integral_mono hi.integrableOn hF.integrableOn (fun x => ?_)).trans (hlocal hg hc ha m (point t p))
      exact Set.indicator_le_self' (fun x _ => hF0 x) x
    · have he : ∀ x∈cell (point t p) t, O.indicator F x=0 := by
        intro x hx
        apply Set.indicator_of_notMem
        intro hxO
        exact hp ⟨x,hxO,hx⟩
      rw [setIntegral_eq_zero_of_forall_eq_zero he]
      exact hB p
  have hbudget (S : Finset (ℤ×ℤ)) : (∑ p∈S,B p) ≤ C*441*(∫ x in Metric.thickening (12*t) K,G x) := by
    simp only [B,← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (usedRegion_budget ht hOK hG hG0 S) hC.le).trans_eq (by ring)
  have hb := integral_cell_budget ht (fun x => ENNReal.ofReal (O.indicator F x)) B hB _ hcell hbudget
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hi0),integral_indicator hO] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

end NullLocalization

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.AbsoluteContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace SobolevBand
open WeakSobolev DiskMaximalTools DiskMoments

lemma high_dyadic (n : ℕ) : high n=2*((2:ℝ)^(2*n)*low n) := by
  have he : 2*n=n+n := by omega
  rw [high,low,he,pow_add]
  field_simp

lemma small_dyadic {L n : ℕ} (hn : L≤n) : 2*low L=2*((2:ℝ)^(n-L)*low n) := by
  have hp : (2:ℝ)^n=2^(n-L)*2^L := by rw [← pow_add,Nat.sub_add_cancel hn]
  rw [low,low,hp]
  field_simp

lemma small_le_high (L n : ℕ) : 2*low L≤high n := by
  have hl : low L≤1 := (inv_le_one₀ (by positivity : (0:ℝ)<2^L)).mpr (one_le_pow₀ (by norm_num))
  have hh : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
  unfold high
  nlinarith

lemma gradient_error_restrict {u : ℕ → ℂ → ℝ} {g : ℂ → ℂ}
    (hu : ∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) (hg : Integrable g)
    (ht : Tendsto (fun n => ∫ x, ‖gradient (u n) x-g x‖) atTop (𝓝 0)) (S : Set ℂ) :
    Tendsto (fun n => ∫ x in S, ‖gradient (u n) x‖) atTop (𝓝 (∫ x in S, ‖g x‖)) := by
  have hi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  apply integral_norm_converges hg.integrableOn (fun n => (hi n).integrableOn)
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) _ ht
  intro n
  exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun x => norm_nonneg _)) ((hi n).sub hg).norm

lemma exists_diagonal_smooth {f : ℂ → ℝ} {g : ℂ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hw : HasGradient (μ := volume) f g) :
    ∃ u : ℕ → ℂ → ℝ, (∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) ∧
      (∀ n, (∫ x,‖gradient (u n) x‖) ≤ (∫ x,‖g x‖)+1) ∧
      Tendsto (fun n => ∫ x,‖gradient (u n) x-g x‖) atTop (𝓝 0) ∧
      (∀ n x, ‖band (u n) (low n) (high n) x-band f (low n) (high n) x‖ ≤ 1/((n:ℝ)+1)) := by
  have he (n : ℕ) : 0 < min (1/((n:ℝ)+1)) (Real.pi*(low n)^2/((n:ℝ)+1)) := by
    have := low_pos n
    apply lt_min <;> positivity
  choose u hu hc he1 he2 using fun n => exists_smooth_compact_approx hf hg hw (he n)
  have hi (n) : Integrable (u n) := (hu n).continuous.integrable_of_hasCompactSupport (hc n)
  have h1 n : ContDiff ℝ 1 (u n) := (hu n).of_le (by simp)
  refine ⟨u,fun n => ⟨h1 n,hc n⟩,?_,?_,?_⟩
  · intro n
    apply (gradient_integral_le (h1 n) (hc n) hg).trans
    gcongr
    have hn : 1/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ((he2 n).le.trans (min_le_left _ _)).trans hn
  · apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => (he2 n).le.trans (min_le_left _ _))
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n x
    rw [Real.norm_eq_abs]
    apply (band_sub_le (hi n) hf (low_pos n) (low_le_high n) x).trans
    have := low_pos n
    apply (div_le_iff₀ (by positivity : 0<Real.pi*(low n)^2)).mpr
    have h := (he1 n).le.trans (min_le_right _ _)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using h

lemma smooth_diagonal_local_L1 {f : ℂ → ℝ} {g : ℂ → ℂ} {u : ℕ → ℂ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hw : HasGradient (μ := volume) f g)
    (hu : ∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n))
    (he : ∀ n x, ‖band (u n) (low n) (high n) x-band (fun y => |f y|) (low n) (high n) x‖ ≤ 1/((n:ℝ)+1))
    {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n => ∫ x in K, ‖band (u n) (low n) (high n) x-maximalComplexReal f x‖) atTop (𝓝 0) := by
  let H := fun n => band (u n) (low n) (high n)
  let A := fun n => band (fun y => |f y|) (low n) (high n)
  have hUi n : Integrable (u n) := (hu n).1.continuous.integrable_of_hasCompactSupport (hu n).2
  have hGi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hH n : Continuous (H n) := (band_lipschitz (hUi n) (hGi n) (contDiff_hasGradient (hu n).1) (low_pos n) (low_le_high n)).continuous
  have hA n : Continuous (A n) := (band_lipschitz hf.abs (abs_gradient_bound hf hg).1 (hw.abs hf hg) (low_pos n) (low_le_high n)).continuous
  have hM := (locallyIntegrable_maximal hf hg hw).integrableOn_isCompact hK
  have hHi n : IntegrableOn (H n) K := (hH n).continuousOn.integrableOn_compact hK
  have hAi n : IntegrableOn (A n) K := (hA n).continuousOn.integrableOn_compact hK
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  have hb (n : ℕ) : (∫ x in K, ‖H n x-maximalComplexReal f x‖) ≤
      (1/((n:ℝ)+1))*volume.real K+(∫ x in K,‖A n x-maximalComplexReal f x‖) := by
    have hcst : (∫ _ : ℂ in K,(1/((n:ℝ)+1)))=(1/((n:ℝ)+1))*volume.real K := by simp only [setIntegral_const,smul_eq_mul,mul_comm]
    have hdiff : IntegrableOn (fun x => ‖A n x-maximalComplexReal f x‖) K := ((hAi n).sub hM).norm
    have hconst : IntegrableOn (fun _ : ℂ => (1/((n:ℝ)+1))) K := integrable_const _
    rw [← hcst,← integral_add hconst hdiff]
    apply integral_mono ((hHi n).sub hM).norm ((integrable_const _).add ((hAi n).sub hM).norm)
    intro x
    change ‖H n x-maximalComplexReal f x‖ ≤ 1/((n:ℝ)+1)+‖A n x-maximalComplexReal f x‖
    exact (norm_sub_le_norm_sub_add_norm_sub (H n x) (A n x) (maximalComplexReal f x)).trans (add_le_add (he n x) le_rfl)
  have hlim : Tendsto (fun n : ℕ => (1/((n:ℝ)+1))*volume.real K+(∫ x in K,‖A n x-maximalComplexReal f x‖)) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_add] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (volume.real K)).add (diagonal_local_L1 hf hg hw hK)
  exact squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hb hlim
end SobolevBand

namespace WeakCompact
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [LocallyCompactSpace X] {μ : Measure X}
lemma densityLimit_compact_bound_limit (w : ℕ → X → ℝ) (hw : ∀ n, Integrable (w n) μ)
    (h0 : ∀ n, ∀ᵐ x ∂μ,0≤w n x) {B : ℝ} (hb : ∀ n,(∫ x,w n x ∂μ)≤B)
    {D : ℝ} {a : ℕ → ℝ} {K O : Set X} (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (ha : ∀ᶠ n in atTop,(∫ x in O,w n x ∂μ)≤a n) (ht : Tendsto a atTop (𝓝 D)) :
    densityLimit w hw h0 hb K ≤ ENNReal.ofReal D := by
  have he (ε : ℝ) (hε : 0<ε) : densityLimit w hw h0 hb K ≤ ENNReal.ofReal (D+ε) := by
    apply densityLimit_compact_bound w hw h0 hb hK hO hKO
    filter_upwards [ha,ht.eventually (gt_mem_nhds (by linarith : D<D+ε))] with n hn hn'
    exact hn.trans hn'.le
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := densityLimit w hw h0 hb K))
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (show Tendsto (fun n : ℕ => D+1/((n:ℝ)+1)) atTop (𝓝 D) by
        simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
  exact Eventually.of_forall (fun n => he _ (by positivity))
end WeakCompact

namespace NullLocalization
open SobolevBand DiskMoments PhysicalCells

lemma thickening_null_integral {K : Set ℂ} (hK : IsCompact K) (hK0 : volume K=0)
    {G : ℂ → ℝ} (hG : Integrable G) :
    Tendsto (fun L => ∫ x in Metric.thickening (12*(2*low L)) K,G x) atTop (𝓝 0) := by
  let s := fun L => Metric.thickening (12*(2*low L)) K
  have hm : Antitone s := fun i j hij => Metric.thickening_mono (by gcongr; exact low_antitone hij) K
  have he : (⋂ L,s L)=K := by
    apply subset_antisymm
    · intro x hx
      apply hK.isClosed.closure_eq ▸ (show x∈closure K from ?_)
      rw [Metric.mem_closure_iff]
      intro ε hε
      have ht : Tendsto (fun L => 12*(2*low L)) atTop (𝓝 0) := by
        simpa only [mul_zero] using (low_tendsto.const_mul 2).const_mul 12
      obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds hε)).exists
      obtain ⟨y,hy,hxy⟩ := Metric.mem_thickening_iff.mp (mem_iInter.mp hx L)
      exact ⟨y,hy,hxy.trans hL⟩
    · exact subset_iInter (fun L => Metric.self_subset_thickening (by have := low_pos L; positivity) K)
  have ht := tendsto_setIntegral_of_antitone (fun L => Metric.isOpen_thickening.measurableSet) hm ⟨0,hG.integrableOn⟩
  rw [he,setIntegral_measure_zero _ hK0] at ht
  exact ht

lemma local_split_bound : ∃ C : ℝ, 0<C ∧ ∀ {u : ℕ → ℂ → ℝ},
    (∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) → ∀ (L : ℕ) {O K : Set ℂ},
    MeasurableSet O → volume O<⊤ → O⊆Metric.thickening (2*low L) K →
    ∀ᶠ n in atTop,
      (∫ x in O,‖gradient (band (u n) (low n) (high n)) x‖) ≤
      C*(∫ x in Metric.thickening (12*(2*low L)) K,‖gradient (u n) x‖)+
        ((∫ x,‖gradient (u n) x‖)/(Real.pi*(2*low L)^2))*volume.real O := by
  obtain ⟨C,hC,hlocal⟩ := smooth_small_local_budget
  refine ⟨C,hC,?_⟩
  intro u hu L O K hO hOf hOK
  have : IsFiniteMeasure (volume.restrict O) := ⟨by simpa using hOf⟩
  filter_upwards [eventually_ge_atTop L] with n hn
  have hat : low n≤2*low L := (low_antitone hn).trans (by have := low_pos L; linarith)
  have hfi := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)
  have hsi := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) hat
  have hcon : IntegrableOn (fun _ : ℂ => (∫ y,‖gradient (u n) y‖)/(Real.pi*(2*low L)^2)) O := integrable_const _
  have hb := integral_mono_ae (hfi.norm.integrableOn (s := O)) (hsi.norm.integrableOn.add hcon)
    (ae_restrict_of_ae (split_gradient (hu n).1 (hu n).2 (low_pos n) hat (small_le_high L n)))
  simp only [Pi.add_apply] at hb
  rw [integral_add hsi.norm.integrableOn hcon,setIntegral_const] at hb
  simp only [smul_eq_mul,mul_comm (volume.real O)] at hb
  apply hb.trans
  gcongr
  have hh := hlocal (hu n).1 (hu n).2 (low_pos n) (n-L) (K := K) hO
  rw [← small_dyadic hn] at hh
  exact hh hOK

lemma diagonal_density_limit_ac {u : ℕ → ℂ → ℝ} {g : ℂ → ℂ}
    (hu : ∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) (hg : Integrable g)
    (ht : Tendsto (fun n => ∫ x,‖gradient (u n) x-g x‖) atTop (𝓝 0))
    (w : ℕ → ℂ → ℝ) (hw : ∀ n, Integrable (w n)) (h0 : ∀ n,∀ᵐ x,0≤w n x)
    {B A : ℝ} (hb : ∀ n,(∫ x,w n x)≤B) (hA : 0≤A)
    (hdom : ∀ n,∀ᵐ x,w n x≤A*‖gradient (band (u n) (low n) (high n)) x‖) :
    WeakCompact.densityLimit w hw h0 hb ≪ volume := by
  have := WeakCompact.densityLimit_regular w hw h0 hb
  apply WeakCompact.absolutelyContinuous_of_compact_null
  intro K hK hK0
  obtain ⟨C,hC,hlocal⟩ := local_split_bound
  let ν := WeakCompact.densityLimit w hw h0 hb
  let V := ∫ x,‖g x‖
  have hi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hv := WeakSobolev.integral_norm_converges hg hi ht
  have hL (L : ℕ) : ν K≤ENNReal.ofReal (A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)) := by
    have he (ε : ℝ) (hε : 0<ε) : ν K≤ENNReal.ofReal
        (A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)+A*(V/(Real.pi*(2*low L)^2))*ε) := by
      obtain ⟨U,hKU,hU,hUf⟩ := K.exists_isOpen_lt_of_lt (μ := (volume : Measure ℂ)) (ENNReal.ofReal ε) (by simpa only [hK0] using ENNReal.ofReal_pos.mpr hε)
      let O := U∩Metric.thickening (2*low L) K
      have hO : IsOpen O := hU.inter Metric.isOpen_thickening
      have hKO : K⊆O := subset_inter hKU (Metric.self_subset_thickening (by have := low_pos L; positivity) K)
      have hOM : volume O≤ENNReal.ofReal ε := (measure_mono inter_subset_left).trans hUf.le
      have hOf : volume O<⊤ := hOM.trans_lt ENNReal.ofReal_lt_top
      have hOB : volume.real O≤ε := by
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hOM).trans_eq (ENNReal.toReal_ofReal hε.le)
      have hgi n : Integrable (fun x => ‖gradient (band (u n) (low n) (high n)) x‖) :=
        (smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)).norm
      have hd n : (∫ x in O,w n x)≤A*(∫ x in O,‖gradient (band (u n) (low n) (high n)) x‖) := by
        rw [← integral_const_mul]
        exact integral_mono_ae (hw n).integrableOn ((hgi n).integrableOn.const_mul A) (ae_restrict_of_ae (hdom n))
      have hh : ν K≤ENNReal.ofReal (A*(C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)+(V/(Real.pi*(2*low L)^2))*volume.real O)) := by
        apply WeakCompact.densityLimit_compact_bound_limit w hw h0 hb hK hO hKO
          (a := fun n => A*(C*(∫ x in Metric.thickening (12*(2*low L)) K,‖gradient (u n) x‖)+((∫ x,‖gradient (u n) x‖)/(Real.pi*(2*low L)^2))*volume.real O))
        · filter_upwards [hlocal hu L hO.measurableSet hOf inter_subset_right] with n hn
          exact (hd n).trans (mul_le_mul_of_nonneg_left hn hA)
        · exact ((gradient_error_restrict hu hg ht _).const_mul C |>.add ((hv.div_const _).mul_const _)).const_mul A
      apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
      have hv0 : 0≤V := integral_nonneg (fun x => norm_nonneg (g x))
      have hcoef : 0≤A*(V/(Real.pi*(2*low L)^2)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hOB hcoef]
    apply le_of_tendsto_of_tendsto (tendsto_const_nhds (x := ν K))
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (show Tendsto (fun n : ℕ => A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖)+A*(V/(Real.pi*(2*low L)^2))*(1/((n:ℝ)+1))) atTop
          (𝓝 (A*C*(∫ x in Metric.thickening (12*(2*low L)) K,‖g x‖))) by
          simpa only [mul_zero,add_zero] using tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _)))
    exact Eventually.of_forall (fun n => he _ (by positivity))
  apply le_antisymm _ bot_le
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((thickening_null_integral hK hK0 hg.norm).const_mul (A*C))
  have hb' := le_of_tendsto_of_tendsto (tendsto_const_nhds (x := ν K)) ht' (Eventually.of_forall hL)
  change ν K ≤ 0
  simpa only [mul_zero,ENNReal.ofReal_zero] using hb'
end NullLocalization

namespace WeakCompact
open CompactlySupported CompactlySupportedContinuousMap

lemma densityLimit_rn (w : ℕ → ℂ → ℝ) (hw : ∀ n,Integrable (w n))
    (h0 : ∀ n,∀ᵐ x,0≤w n x) {B D : ℝ} (hb : ∀ n,(∫ x,w n x)≤B) (hB : 0≤B)
    (hac : densityLimit w hw h0 hb ≪ volume)
    (hm : densityLimit w hw h0 hb univ≤ENNReal.ofReal D) (hD : 0≤D) :
    ∃ d : ℂ → ℝ, Integrable d ∧ (∀ x,0≤d x) ∧ (∫ x,d x)≤D ∧
      ∀ φ : C_c(ℂ,ℝ), Tendsto (fun n => ∫ x,w n x*φ x) (hyperfilter ℕ) (𝓝 (∫ x,d x*φ x)) := by
  let ν := densityLimit w hw h0 hb
  have : IsFiniteMeasure ν := densityLimit_finite w hw h0 hb hB
  let d := fun x => (ν.rnDeriv volume x).toReal
  have hi : Integrable d := by
    have h := Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := volume) (s := univ) (measure_ne_top ν univ)
    simpa only [integrableOn_univ] using h
  refine ⟨d,hi,fun x => ENNReal.toReal_nonneg,?_,?_⟩
  · rw [show (∫ x,d x)=ν.real univ from Measure.integral_toReal_rnDeriv hac]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hm).trans_eq (ENNReal.toReal_ofReal hD)
  · intro φ
    rw [show (∫ x,d x*φ x)=(∫ x,φ x ∂ν) from integral_toReal_rnDeriv_mul hac]
    exact densityLimit_integral w hw h0 hb φ
end WeakCompact

namespace WeakSobolev
lemma local_L1_test_converges {F : ℂ → ℝ} {u : ℕ → ℂ → ℝ}
    (hF : LocallyIntegrable F) (hu : ∀ n,LocallyIntegrable (u n))
    (ht : ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => ∫ x in K,‖u n x-F x‖) atTop (𝓝 0))
    {φ : ℂ → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x,u n x*φ x) atTop (𝓝 (∫ x,F x*φ x)) := by
  let K := tsupport φ
  have hK : IsCompact K := hc
  have hFm : IntegrableOn F K := hF.integrableOn_isCompact hK
  have hum n : IntegrableOn (u n) K := (hu n).integrableOn_isCompact hK
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hφ
  have hlim := bounded_smul_converges hFm hum (ht K hK) hφ.aestronglyMeasurable.restrict (ae_of_all _ hB)
  have hi n : IntegrableOn (fun x => φ x*u n x) K := (hum n).bdd_smul B hφ.aestronglyMeasurable.restrict (ae_of_all _ hB)
  have hf : IntegrableOn (fun x => φ x*F x) K := hFm.bdd_smul B hφ.aestronglyMeasurable.restrict (ae_of_all _ hB)
  have hh := integral_converges_norm hf hi hlim
  have he (v : ℂ → ℝ) : (∫ x in K,φ x*v x)=(∫ x,v x*φ x) := by
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      by_cases hx : x∈K
      · rw [indicator_of_mem hx,mul_comm]
      · rw [indicator_of_notMem hx]
        simp only [image_eq_zero_of_notMem_tsupport hx,mul_zero])
  simpa only [he,smul_eq_mul] using hh
end WeakSobolev

namespace SobolevBand
open WeakSobolev WeakCompact CompactlySupported CompactlySupportedContinuousMap DiskMoments

/-- Positive directional densities share a single ultrafilter, so their differences
retain the distributional identities. Absolute continuity is proved by local
small-radius cutoff estimates, rather than assumed as a BV compactness upgrade. -/
lemma positive_direction_limit : ∃ C : ℝ, 0<C ∧
    ∀ {u : ℕ → ℂ → ℝ} {g : ℂ → ℂ},
    (∀ n, ContDiff ℝ 1 (u n) ∧ HasCompactSupport (u n)) → Integrable g →
    (∀ n, (∫ x,‖gradient (u n) x‖)≤(∫ x,‖g x‖)+1) →
    Tendsto (fun n => ∫ x,‖gradient (u n) x-g x‖) atTop (𝓝 0) →
    ∀ v : ℂ, ‖v‖≤1 → ∃ d : ℂ → ℝ, Integrable d ∧ (∀ x,0≤d x) ∧
      (∫ x,d x)≤2*C*(∫ x,‖g x‖) ∧
      ∀ φ : C_c(ℂ,ℝ), Tendsto
        (fun n => ∫ x,(‖gradient (band (u n) (low n) (high n)) x‖+
          ⟪gradient (band (u n) (low n) (high n)) x,v⟫)*φ x)
        (hyperfilter ℕ) (𝓝 (∫ x,d x*φ x)) := by
  obtain ⟨C,hC,hbound⟩ := smooth_dyadic_bound
  refine ⟨C,hC,?_⟩
  intro u g hu hg hV ht v hv
  let q := fun n => gradient (band (u n) (low n) (high n))
  let w := fun n x => ‖q n x‖+⟪q n x,v⟫
  let V := ∫ x,‖g x‖
  have hV0 : 0≤V := integral_nonneg (fun x => norm_nonneg _)
  have hqi n : Integrable (q n) := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)
  have hwi n : Integrable (w n) := (hqi n).norm.add ((hqi n).inner_const (𝕜 := ℝ) v)
  have hinner n x : |⟪q n x,v⟫|≤‖q n x‖ :=
    (abs_real_inner_le_norm (q n x) v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)
  have hw0 n : ∀ᵐ x,0≤w n x := ae_of_all _ (fun x => by
    dsimp only [w]
    have := (abs_le.mp (hinner n x)).1
    linarith)
  have hdom n : ∀ᵐ x,w n x≤2*‖q n x‖ := ae_of_all _ (fun x => by
    dsimp only [w]
    have := (abs_le.mp (hinner n x)).2
    linarith)
  have hmass n : (∫ x,w n x)≤2*C*(∫ x,‖gradient (u n) x‖) := by
    have h := hbound (hu n).1 (hu n).2 (low_pos n) (2*n)
    rw [← high_dyadic n] at h
    calc
      (∫ x,w n x) ≤ ∫ x,2*‖q n x‖ := integral_mono_ae (hwi n) ((hqi n).norm.const_mul 2) (hdom n)
      _ = 2*(∫ x,‖q n x‖) := integral_const_mul _ _
      _ ≤ 2*(C*(∫ x,‖gradient (u n) x‖)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hb n : (∫ x,w n x)≤2*C*(V+1) :=
    (hmass n).trans (mul_le_mul_of_nonneg_left (hV n) (by positivity))
  have hac := NullLocalization.diagonal_density_limit_ac hu hg ht w hwi hw0 hb (by norm_num : (0:ℝ)≤2) hdom
  have hi n : Integrable (gradient (u n)) := (continuous_gradient (hu n).1).integrable_of_hasCompactSupport (gradient_hasCompactSupport (hu n).2)
  have hsharp := densityLimit_sharp_mass w hwi hw0 hb hmass
    ((integral_norm_converges hg hi ht).const_mul (2*C))
  exact densityLimit_rn w hwi hw0 hb (by positivity) hac hsharp (by positivity)
end SobolevBand

namespace WeakSobolev
open CompactlySupported CompactlySupportedContinuousMap

lemma direction_identity_limit {F : ℂ → ℝ} {H : ℕ → ℂ → ℝ} {q : ℕ → ℂ → ℂ}
    (hF : LocallyIntegrable F) (hH : ∀ n, LocallyIntegrable (H n))
    (hqi : ∀ n, Integrable (q n)) (hw : ∀ n, HasGradient (μ := volume) (H n) (q n))
    (ht : ∀ K : Set ℂ, IsCompact K → Tendsto (fun n => ∫ x in K,‖H n x-F x‖) atTop (𝓝 0))
    {d e : ℂ → ℝ} (hd : Integrable d) (he : Integrable e) (v : ℂ)
    (hv : ∀ φ : C_c(ℂ,ℝ), Tendsto (fun n => ∫ x,(‖q n x‖+⟪q n x,v⟫)*φ x)
      (hyperfilter ℕ) (𝓝 (∫ x,d x*φ x)))
    (h0 : ∀ φ : C_c(ℂ,ℝ), Tendsto (fun n => ∫ x,(‖q n x‖+⟪q n x,(0:ℂ)⟫)*φ x)
      (hyperfilter ℕ) (𝓝 (∫ x,e x*φ x))) :
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,F x*fderiv ℝ φ x v) = -∫ x,(d x-e x)*φ x := by
  intro φ hφ hc
  let φ' : C_c(ℂ,ℝ) := ⟨⟨φ,hφ.continuous⟩,hc⟩
  have hn n : Integrable (fun x => ‖q n x‖*φ x) :=
    (hqi n).norm.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hp n : Integrable (fun x => (‖q n x‖+⟪q n x,v⟫)*φ x) :=
    ((hqi n).norm.add ((hqi n).inner_const (𝕜 := ℝ) v)).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hd' : Integrable (fun x => d x*φ x) := hd.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have he' : Integrable (fun x => e x*φ x) := he.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hvn n : (∫ x,(‖q n x‖+⟪q n x,v⟫)*φ x)-(∫ x,(‖q n x‖+⟪q n x,(0:ℂ)⟫)*φ x) =
      ∫ x,⟪q n x,v⟫*φ x := by
    simp only [inner_zero_right,add_zero]
    rw [← integral_sub (hp n) (hn n)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hde : (∫ x,d x*φ x)-(∫ x,e x*φ x) = ∫ x,(d x-e x)*φ x := by
    rw [← integral_sub hd' he']
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  have hlim : Tendsto (fun n => ∫ x,H n x*fderiv ℝ φ x v) (hyperfilter ℕ)
      (𝓝 (-∫ x,(d x-e x)*φ x)) := by
    have h := ((hv φ').sub (h0 φ')).neg
    change Tendsto (fun n => -((∫ x,(‖q n x‖+⟪q n x,v⟫)*φ x)-(∫ x,(‖q n x‖+⟪q n x,(0:ℂ)⟫)*φ x)))
      (hyperfilter ℕ) (𝓝 (-((∫ x,d x*φ x)-(∫ x,e x*φ x)))) at h
    simp only [hvn,hde,← hw _ φ hφ hc v] at h
    exact h
  exact tendsto_nhds_unique
    ((local_L1_test_converges hF hH ht ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ v)).mono_left Nat.hyperfilter_le_atTop) hlim

lemma complex_inner_one (z : ℂ) : ⟪z,(1:ℂ)⟫=(z.re:ℝ) := by
  simp [real_inner_eq_re_inner, RCLike.inner_apply]
lemma complex_inner_I (z : ℂ) : ⟪z,Complex.I⟫=(z.im:ℝ) := by
  simp [real_inner_eq_re_inner, RCLike.inner_apply]

lemma complex_hasGradient_of_coordinates {F : ℂ → ℝ} {G : ℂ → ℂ}
    (hF : LocallyIntegrable F) (hG : Integrable G)
    (h1 : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,F x*fderiv ℝ φ x 1) = -∫ x,(G x).re*φ x)
    (hI : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,F x*fderiv ℝ φ x Complex.I) = -∫ x,(G x).im*φ x) :
    HasGradient (μ := volume) F G := by
  intro φ hφ hc v
  have hv : v=v.re • (1:ℂ)+v.im • Complex.I := by simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  have hh w : Integrable (fun x => F x*fderiv ℝ φ x w) :=
    hF.integrable_smul_right_of_hasCompactSupport ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ w)
  have hg1 : Integrable (fun x => (G x).re*φ x) :=
    (hG.inner_const (𝕜 := ℝ) (1:ℂ)).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc |>.congr (ae_of_all _ (fun x => by simp only [complex_inner_one,smul_eq_mul]))
  have hgI : Integrable (fun x => (G x).im*φ x) :=
    (hG.inner_const (𝕜 := ℝ) Complex.I).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc |>.congr (ae_of_all _ (fun x => by simp only [complex_inner_I,smul_eq_mul]))
  have hfder x : F x*fderiv ℝ φ x v=v.re*(F x*fderiv ℝ φ x 1)+v.im*(F x*fderiv ℝ φ x Complex.I) := by
    conv_lhs => rw [hv]
    simp only [map_add,map_smul,smul_eq_mul]
    ring
  have hinner x : ⟪G x,v⟫*φ x=v.re*((G x).re*φ x)+v.im*((G x).im*φ x) := by
    conv_lhs => rw [hv]
    rw [inner_add_right,real_inner_smul_right,real_inner_smul_right,complex_inner_one,complex_inner_I]
    ring
  simp_rw [hfder,hinner]
  rw [integral_add ((hh 1).const_mul _) ((hh Complex.I).const_mul _),
    integral_add (hg1.const_mul _) (hgI.const_mul _)]
  simp only [integral_const_mul,h1 φ hφ hc,hI φ hφ hc]
  ring
end WeakSobolev

namespace SobolevBand
open WeakSobolev DiskMaximalTools DiskMoments

/-- The all-radius absolute endpoint on the isometric complex model of the plane.
No smoothness, sign, compact support, or boundedness remains on the input. -/
lemma complex_endpoint : ∃ C : ℝ, 0<C ∧ ∀ (f : ℂ → ℝ) (g : ℂ → ℂ),
    Integrable f → Integrable g → HasGradient (μ := volume) f g →
    LocallyIntegrable (maximalComplexReal f) ∧ ∃ G : ℂ → ℂ,
      Integrable G ∧ HasGradient (μ := volume) (maximalComplexReal f) G ∧
        (∫ x,‖G x‖)≤C*(∫ x,‖g x‖) := by
  obtain ⟨C,hC,hlim⟩ := positive_direction_limit
  refine ⟨8*C,by positivity,?_⟩
  intro f g hf hg hw
  let a := fun x => absCoefficient (f x) • g x
  have ha : Integrable a := (abs_gradient_bound hf hg).1
  obtain ⟨u,hu,hV,ht,he⟩ := exists_diagonal_smooth hf.abs ha (hw.abs hf hg)
  let H := fun n => band (u n) (low n) (high n)
  let q := fun n => gradient (H n)
  have hqi n : Integrable (q n) := smooth_band_integrable_gradient (hu n).1 (hu n).2 (low_pos n) (low_le_high n)
  have hH n : LocallyIntegrable (H n) := (smooth_band_lipschitz (hu n).1 (hu n).2 (low_pos n) (low_le_high n)).continuous.locallyIntegrable
  have hwH n : HasGradient (μ := volume) (H n) (q n) :=
    lipschitz_hasGradient (smooth_band_lipschitz (hu n).1 (hu n).2 (low_pos n) (low_le_high n))
  have hF := locallyIntegrable_maximal hf hg hw
  have htH (K : Set ℂ) (hK : IsCompact K) :
      Tendsto (fun n => ∫ x in K,‖H n x-maximalComplexReal f x‖) atTop (𝓝 0) :=
    smooth_diagonal_local_L1 hf hg hw hu he hK
  obtain ⟨d0,hd0,h0pos,h0mass,h0lim⟩ := hlim hu ha hV ht 0 (by simp)
  obtain ⟨d1,hd1,h1pos,h1mass,h1lim⟩ := hlim hu ha hV ht 1 (by simp)
  obtain ⟨dI,hdI,hIpos,hImass,hIlim⟩ := hlim hu ha hV ht Complex.I (by simp)
  let G := fun x => ((d1 x-d0 x : ℝ):ℂ)+((dI x-d0 x : ℝ):ℂ)*Complex.I
  have hG : Integrable G := ((hd1.sub hd0).ofReal).add (((hdI.sub hd0).ofReal).mul_const Complex.I)
  have hGre x : (G x).re=d1 x-d0 x := by simp [G]
  have hGim x : (G x).im=dI x-d0 x := by simp [G]
  refine ⟨hF,G,hG,?_,?_⟩
  · apply complex_hasGradient_of_coordinates hF hG
    · simpa only [hGre] using direction_identity_limit hF hH hqi hwH htH hd1 hd0 1 h1lim h0lim
    · simpa only [hGim] using direction_identity_limit hF hH hqi hwH htH hdI hd0 Complex.I hIlim h0lim
  · have hb x : ‖G x‖≤d1 x+dI x+2*d0 x := by
      have h := Complex.norm_le_abs_re_add_abs_im (G x)
      rw [hGre,hGim] at h
      have h1 : |d1 x-d0 x| ≤ d1 x+d0 x := by
        exact abs_le.mpr ⟨by linarith [h1pos x,h0pos x],by linarith [h1pos x,h0pos x]⟩
      have hI : |dI x-d0 x| ≤ dI x+d0 x := by
        exact abs_le.mpr ⟨by linarith [hIpos x,h0pos x],by linarith [hIpos x,h0pos x]⟩
      linarith
    have hi := integral_mono hG.norm ((hd1.add hdI).add (hd0.const_mul 2)) hb
    simp only [Pi.add_apply] at hi
    rw [integral_add (f := fun x => d1 x+dI x) (hd1.add hdI) (hd0.const_mul 2),integral_add hd1 hdI,integral_const_mul] at hi
    have hba : (∫ x,‖a x‖)≤∫ x,‖g x‖ := (abs_gradient_bound hf hg).2
    have hh : (∫ x,‖G x‖)≤8*C*(∫ x,‖a x‖) := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_left hba (by positivity))
end SobolevBand

namespace WeakSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma HasGradient.comp_isometry {f : F → ℝ} {g : F → F}
    (hw : HasGradient (μ := volume) f g) (e : E ≃ₗᵢ[ℝ] F) :
    HasGradient (μ := volume) (fun x => f (e x)) (fun x => e.symm (g (e x))) := by
  intro φ hφ hc v
  let ψ := φ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hd x : fderiv ℝ ψ (e x) (e v)=fderiv ℝ φ x v := by
    rw [fderiv_comp (e x) (hφ.differentiable (by simp) _) (e.symm.differentiableAt),e.symm.fderiv]
    change fderiv ℝ φ (e.symm (e x)) (e.symm (e v))=fderiv ℝ φ x v
    simp only [e.symm_apply_apply]
  have hi x : ⟪e.symm (g (e x)),v⟫=⟪g (e x),e v⟫ := by
    simpa only [e.apply_symm_apply] using (e.inner_map_map (e.symm (g (e x))) v).symm
  have h := hw ψ hψ hψc (e v)
  rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => f y*fderiv ℝ ψ y (e v)),
    ← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding (fun y => ⟪g y,e v⟫*ψ y)] at h
  simpa only [hd,← hi,ψ,Function.comp_apply,e.symm_apply_apply] using h
end WeakSobolev

end

end OAI
end

section
-- module Solutions.OAIQW_DiskMaximal.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace CenteredDiskEndpoint
open WeakSobolev

lemma hasGradient_iff_hasWeakGradient {f : Plane → ℝ} {g : Plane → Plane}
    (hf : LocallyIntegrable f) (hg : Integrable g) :
    HasGradient (μ := volume) f g ↔ HasWeakGradient f g := by
  constructor
  · intro hw φ hφ hc i
    simpa only [testPartial,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul]
      using hw φ hφ hc (EuclideanSpace.single i 1)
  · intro hw φ hφ hc v
    have hv : v=∑ i : Fin 2,v i • EuclideanSpace.single i 1 := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v).symm
    have hleft i : Integrable (fun x => f x*testPartial φ i x) :=
      hf.integrable_smul_right_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
    have hright i : Integrable (fun x => g x i*φ x) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hg).locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
    have hd x : f x*fderiv ℝ φ x v=∑ i : Fin 2,v i*(f x*testPartial φ i x) := by
      conv_lhs => rw [hv]
      simp only [_root_.map_sum,map_smul,smul_eq_mul,Finset.mul_sum,testPartial]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hi x : ⟪g x,v⟫*φ x=∑ i : Fin 2,v i*(g x i*φ x) := by
      conv_lhs => rw [hv]
      simp only [inner_sum,real_inner_smul_right,EuclideanSpace.inner_single_right,RCLike.conj_to_real,one_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hd,hi]
    rw [integral_finsetSum _ (fun i _ => (hleft i).const_mul _),
      integral_finsetSum _ (fun i _ => (hright i).const_mul _)]
    simp only [integral_const_mul,hw φ hφ hc,Finset.sum_neg_distrib,mul_neg]

lemma integrable_comp_complexPlane {F : Type*} [NormedAddCommGroup F] {f : Plane → F} :
    Integrable (fun z => f (complexPlane z)) ↔ Integrable f :=
  complexPlane.measurePreserving.integrable_comp_emb complexPlane.toMeasurableEquiv.measurableEmbedding

lemma integrable_comp_complexPlane_symm {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    Integrable (fun x => f (complexPlane.symm x)) ↔ Integrable f :=
  complexPlane.symm.measurePreserving.integrable_comp_emb complexPlane.symm.toMeasurableEquiv.measurableEmbedding

lemma locallyIntegrable_comp_complexPlane {f : Plane → ℝ} :
    LocallyIntegrable (fun z => f (complexPlane z)) ↔ LocallyIntegrable f := by
  have h := locallyIntegrable_map_homeomorph complexPlane.toHomeomorph (f := f) (μ := volume)
  change LocallyIntegrable f (Measure.map complexPlane volume) ↔ LocallyIntegrable (fun z => f (complexPlane z)) at h
  rw [complexPlane.measurePreserving.map_eq] at h
  exact h.symm

lemma gradientNorm_comp_complexPlane (g : Plane → Plane) :
    (∫ z,‖complexPlane.symm (g (complexPlane z))‖)=gradientNorm g := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.measurePreserving.integral_comp complexPlane.toMeasurableEquiv.measurableEmbedding (fun x => ‖g x‖)

lemma gradientNorm_comp_complexPlane_symm (G : ℂ → ℂ) :
    gradientNorm (fun x => complexPlane (G (complexPlane.symm x)))=∫ z,‖G z‖ := by
  simp only [LinearIsometryEquiv.norm_map,gradientNorm]
  exact complexPlane.symm.measurePreserving.integral_comp complexPlane.symm.toMeasurableEquiv.measurableEmbedding (fun z => ‖G z‖)
end CenteredDiskEndpoint

namespace CenteredDiskEndpoint
open WeakSobolev DiskMaximalTools

/-- Equality of the actual all-real-radius operators, including the normalization
and absolute values. This bridge has no regularity assumption on the input. -/
lemma maximalComplex_comp_complexPlane (f : Plane → ℝ) (z : ℂ) :
    maximalComplex (fun w => f (complexPlane w)) z=maximal f (complexPlane z) := by
  rw [maximalComplex_eq_all_radii,maximal]
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  rw [absoluteDiskAverage,absoluteMeasure,withDensity_apply _ measurableSet_ball,
    volume_disk_real z hr.le]
  congr 1
  have h := complexPlane.measurePreserving.setLIntegral_comp_emb
    complexPlane.toMeasurableEquiv.measurableEmbedding (fun x => ENNReal.ofReal |f x|) (Metric.ball z r)
  rw [complexPlane.image_ball] at h
  exact h

lemma maximalComplexReal_comp_complexPlane (f : Plane → ℝ) :
    DiskMaximalTools.maximalComplexReal (fun w => f (complexPlane w)) = fun z => maximalReal f (complexPlane z) := by
  funext z
  exact congrArg ENNReal.toReal (maximalComplex_comp_complexPlane f z)

theorem main_endpoint_oai : EndpointStatement := by
  obtain ⟨C,hC,hendpoint⟩ := SobolevBand.complex_endpoint
  refine ⟨C,hC.le,?_⟩
  intro f g hf hg hw
  let f' := fun z => f (complexPlane z)
  let g' := fun z => complexPlane.symm (g (complexPlane z))
  have hf' : Integrable f' := integrable_comp_complexPlane.mpr hf
  have hg0 : Integrable (fun z => g (complexPlane z)) := integrable_comp_complexPlane.mpr hg
  have hg' : Integrable g' := complexPlane.symm.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hg0
  have hw0 : HasGradient (μ := volume) f g := (hasGradient_iff_hasWeakGradient hf.locallyIntegrable hg).mpr hw
  have hw' : HasGradient (μ := volume) f' g' := hw0.comp_isometry complexPlane
  obtain ⟨hM',G',hG'i,hwG',hbound⟩ := hendpoint f' g' hf' hg' hw'
  have he : maximalComplexReal f'=fun z => maximalReal f (complexPlane z) := maximalComplexReal_comp_complexPlane f
  rw [he] at hM'
  have hM : LocallyIntegrable (maximalReal f) := locallyIntegrable_comp_complexPlane.mp hM'
  let G := fun x => complexPlane (G' (complexPlane.symm x))
  have hG0 : Integrable (fun x => G' (complexPlane.symm x)) := integrable_comp_complexPlane_symm.mpr hG'i
  have hG : Integrable G := complexPlane.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hG0
  have hwG0 := hwG'.comp_isometry complexPlane.symm
  have hwG : HasWeakGradient (maximalReal f) G := by
    apply (hasGradient_iff_hasWeakGradient hM hG).mp
    simpa only [he,complexPlane.apply_symm_apply,LinearIsometryEquiv.symm_symm] using hwG0
  refine ⟨ae_maximal_ne_top hf,hM,inW11Loc_of_gradient hM hG hwG,G,hG,hwG,?_⟩
  rw [show gradientNorm G=∫ z,‖G' z‖ from gradientNorm_comp_complexPlane_symm G']
  exact hbound.trans_eq (congrArg (fun v => C*v) (gradientNorm_comp_complexPlane g))
end CenteredDiskEndpoint

end

end OAI
end

theorem solution : type_of% @OAI.CenteredDiskEndpoint.main_endpoint_oai := @OAI.CenteredDiskEndpoint.main_endpoint_oai
