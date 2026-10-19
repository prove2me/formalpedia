-- Prove2me | solution 2 for OAI.Problem356.SmoothBranchMarginal.exists_smooth_branch_marginal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:51:28.940831+00:00
-- url     : https://prove2.me/submissions/18b4f315-08e7-4556-8485-239e5f277d20

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal

open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal
open MeasureTheory Set
open scoped ENNReal
theorem h41_bump (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ g : E3 → ℝ,
      (∀ x, 0 ≤ g x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
      HasCompactSupport g ∧
      tsupport g ⊆ Metric.ball c r ∧
      (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  let f : ContDiffBump c := ⟨r/4, r/2, by positivity, by linarith⟩
  set I := ∫ x : E3, (f x) ^ 2 with hI
  have hcont : Continuous fun x => (f x) ^ 2 := f.continuous.pow 2
  have hcs : HasCompactSupport fun x => (f x) ^ 2 :=
    f.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hint : MeasureTheory.Integrable (fun x => (f x) ^ 2) (volume : Measure E3) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hsupp : Function.support (fun x => (f x) ^ 2) = Metric.ball c (r/2) := by
    rw [← f.support_eq]; ext x; simp [Function.mem_support]
  have hIpos : 0 < I := by
    rw [hI, integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint, hsupp]
    exact Metric.measure_ball_pos _ _ (by positivity)
  refine ⟨fun x => (√I)⁻¹ * f x, fun x => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (f.nonneg),
    contDiff_const.mul f.contDiff, f.hasCompactSupport.mul_left, ?_, ?_⟩
  · refine (tsupport_mul_subset_right).trans ?_
    rw [f.tsupport_eq]
    exact Metric.closedBall_subset_ball (show r / 2 < r by linarith)
  · simp only [mul_pow]
    rw [integral_const_mul, inv_pow, Real.sq_sqrt hIpos.le, ← hI]
    exact inv_mul_cancel₀ hIpos.ne'




open scoped BigOperators in
theorem h41_dsw {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hgm : ∀ i ∈ s, Measurable (g i)) :
    densityMeasure (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) • densityMeasure (fun x => (g i x) ^ 2) := by
  ext A hA
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, densityMeasure, withDensity_apply _ hA, smul_eq_mul]
  have hpt : ∀ x, ENNReal.ofReal (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, ENNReal.ofReal (a i) * ENNReal.ofReal ((g i x) ^ 2) := by
    intro x
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))]
    exact Finset.sum_congr rfl (fun i hi => ENNReal.ofReal_mul (ha i hi))
  simp_rw [hpt]
  rw [lintegral_finsetSum s (fun i hi => (((hgm i hi).pow_const 2).ennreal_ofReal).const_mul _)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact lintegral_const_mul _ ((hgm i hi).pow_const 2).ennreal_ofReal


theorem pb_sqrt_sum {ι X : Type*} (s : Finset ι)
    (a : ι → ℝ) (g : ι → X → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (x : X) :
    Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2) =
      ∑ i ∈ s, Real.sqrt (a i) * g i x := by
  classical
  by_cases hx : ∃ i ∈ s, g i x ≠ 0
  · obtain ⟨i, hi, hgi⟩ := hx
    have hz : ∀ j ∈ s, j ≠ i → g j x = 0 := by
      intro j hj hji
      by_contra hne
      exact Set.disjoint_left.mp (hd j hj i hi hji) (Function.mem_support.mpr hne) (Function.mem_support.mpr hgi)
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji]; ring),
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => by rw [hz j hj hji]; ring)]
    rw [Real.sqrt_mul (ha i hi), Real.sqrt_sq (hg i hi x)]
  · push Not at hx
    rw [Finset.sum_eq_zero (fun j hj => by rw [hx j hj]; ring),
      Finset.sum_eq_zero (fun j hj => by rw [hx j hj]; ring)]
    simp

theorem pb_hcs_sum {ι X : Type*} [TopologicalSpace X] (s : Finset ι) (f : ι → X → ℝ)
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  have hK : IsCompact (⋃ i ∈ s, tsupport (f i)) := s.isCompact_biUnion (fun i hi => h i hi)
  have hKc : IsClosed (⋃ i ∈ s, tsupport (f i)) :=
    s.finite_toSet.isClosed_biUnion (fun i _ => isClosed_tsupport _)
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (closure_minimal ?_ hKc)
  intro x hx
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact Set.mem_biUnion hi (subset_tsupport _ hne)

theorem pb_main {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hmass : (∫ x : E3, (∑ i ∈ s, a i * (g i x) ^ 2)
      ∂(volume : Measure E3)) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  refine ⟨fun x => Finset.sum_nonneg (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _)), ?_, ?_, ?_, ?_, hmass⟩
  · exact ContDiff.sum (fun i hi => contDiff_const.mul ((hsm i hi).pow 2))
  · refine pb_hcs_sum s _ (fun i hi => (hcs i hi).mono ?_)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; apply hx; rw [h0]; ring
  · have e : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) = fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x :=
      funext (pb_sqrt_sum s a g ha hg hd)
    rw [e]
    exact ContDiff.sum (fun i hi => contDiff_const.mul (hsm i hi))
  · have e : (fun x => Real.sqrt (∑ i ∈ s, a i * (g i x) ^ 2)) = fun x => ∑ i ∈ s, Real.sqrt (a i) * g i x :=
      funext (pb_sqrt_sum s a g ha hg hd)
    rw [e]
    refine pb_hcs_sum s _ (fun i hi => (hcs i hi).mono ?_)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; apply hx; rw [h0]; ring

open scoped BigOperators in
theorem h41_scpd
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (g : ι → E3 → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (hg : ∀ i ∈ s, ∀ x, 0 ≤ g i x)
    (hsm : ∀ i ∈ s, ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (g i))
    (hcs : ∀ i ∈ s, HasCompactSupport (g i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (Function.support (g i)) (Function.support (g j)))
    (hgint : ∀ i ∈ s, (∫ x : E3, (g i x) ^ 2 ∂(volume : Measure E3)) = 1)
    (haint : (∑ i ∈ s, a i) = 1) :
    IsSmoothCompactProbabilityDensity (fun x => ∑ i ∈ s, a i * (g i x) ^ 2) := by
  apply pb_main s a g ha hg hsm hcs hd
  have hint : ∀ i ∈ s, Integrable (fun x : E3 => a i * g i x ^ 2) volume := by
    intro i hi
    have hc : Continuous (fun x : E3 => a i * g i x ^ 2) := by
      have := (hsm i hi).continuous
      fun_prop
    refine hc.integrable_of_hasCompactSupport ((hcs i hi).mono ?_)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h0; apply hx; rw [h0]; ring
  rw [integral_finsetSum s hint]
  rw [← haint]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [integral_const_mul, hgint i hi, mul_one]


open OAI OAI.Problem356 MeasureTheory in
theorem h41_mwd (e : OpenPartialHomeomorph E3 E3) (w : E3 → ENNReal)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by
  have hae : AEMeasurable e (((volume : Measure E3).restrict e.source).withDensity w) := by
    have : AEMeasurable e ((volume : Measure E3).restrict e.source) :=
      e.continuousOn.aemeasurable e.open_source.measurableSet
    exact this.mono_ac (withDensity_absolutelyContinuous _ _)
  ext A hA
  rw [Measure.map_apply_of_aemeasurable hae hA, withDensity_apply' _ _, withDensity_apply _ hA,
    Measure.restrict_restrict' e.open_source.measurableSet,
    Measure.restrict_restrict' e.open_target.measurableSet]
  have hs : MeasurableSet (e.target ∩ A) := e.open_target.measurableSet.inter hA
  have himg : e.symm '' (e.target ∩ A) = e ⁻¹' A ∩ e.source := by
    exact (e.toPartialEquiv.symm_image_target_inter_eq' A).trans (Set.inter_comm _ _)
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure E3) hs
    (f := e.symm) (f' := D)
    (fun y hy => (hD y hy.1).hasFDerivWithinAt) (e.symm.injOn.mono Set.inter_subset_left) w
  rw [himg] at hcv
  rw [hcv, Set.inter_comm]

open OAI OAI.Problem356 MeasureTheory Set Filter in
theorem h41_msd
    (e : OpenPartialHomeomorph E3 E3) (g : E3 → ℝ)
    (hgs : tsupport g ⊆ e.source)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y =>
        localTransportAmplitude e g (fun z => Real.sqrt |(D z).det|) y ^ 2) := by
  have h1 : densityMeasure (fun x => g x ^ 2) =
      ((volume : Measure E3).restrict e.source).withDensity (fun x => ENNReal.ofReal (g x ^ 2)) := by
    rw [densityMeasure, ← withDensity_indicator e.open_source.measurableSet]
    congr 1
    refine (Set.indicator_eq_self.mpr ?_).symm
    intro x hx
    apply hgs
    apply subset_tsupport
    intro h0
    apply hx
    simp [h0]
  rw [h1, h41_mwd e _ D hD, densityMeasure]
  have h2 : (fun y => ENNReal.ofReal (localTransportAmplitude e g (fun z => Real.sqrt |(D z).det|) y ^ 2)) =
      e.target.indicator (fun y => ENNReal.ofReal |(D y).det| * ENNReal.ofReal (g (e.symm y) ^ 2)) := by
    funext y
    by_cases hy : y ∈ e.target
    · rw [Set.indicator_of_mem hy, localTransportAmplitude, Set.indicator_of_mem hy, mul_pow,
        Real.sq_sqrt (abs_nonneg _), mul_comm, ENNReal.ofReal_mul (abs_nonneg _)]
    · rw [Set.indicator_of_notMem hy, localTransportAmplitude, Set.indicator_of_notMem hy]
      simp
  rw [h2, withDensity_indicator e.open_target.measurableSet]

theorem h41_tsa
    (e : OpenPartialHomeomorph E3 E3) {g : E3 → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ e.source)
    (hmass : (∫ x : E3, g x ^ 2) = 1)
    (he : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) e.symm e.target)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y)
    (hJ : ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D y).det|) e.target) :
    ∃ q : E3 → ℝ,
      (∀ y, 0 ≤ q y) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q ∧
      HasCompactSupport q ∧
      tsupport q ⊆ e '' tsupport g ∧
      (∫ y : E3, q y ^ 2) = 1 ∧
      Measure.map (LocalBranchMeasure.extendedBranch e 0)
        (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) := by
  classical
  set J : E3 → ℝ := fun y => Real.sqrt |(D y).det| with hJdef
  set q : E3 → ℝ := localTransportAmplitude e g J with hqdef
  have hK : IsCompact (tsupport g) := hgc
  have hKe : IsCompact (e '' tsupport g) := hK.image_of_continuousOn (e.continuousOn.mono hgs)
  have hKt : e '' tsupport g ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hgs hx)
  have hzero : ∀ y, y ∉ e '' tsupport g → q y = 0 := by
    intro y hy
    simp only [hqdef, localTransportAmplitude]
    by_cases ht : y ∈ e.target
    · rw [Set.indicator_of_mem ht]
      have : g (e.symm y) = 0 := by
        by_contra h0
        exact hy ⟨e.symm y, subset_tsupport _ h0, e.right_inv ht⟩
      rw [this, zero_mul]
    · exact Set.indicator_of_notMem ht _
  have hsupp : tsupport q ⊆ e '' tsupport g := by
    refine closure_minimal ?_ hKe.isClosed
    intro y hy
    by_contra h
    exact hy (hzero y h)
  have hq0 : ∀ y, 0 ≤ q y := by
    intro y
    simp only [hqdef, localTransportAmplitude]
    by_cases ht : y ∈ e.target
    · rw [Set.indicator_of_mem ht]; exact mul_nonneg (hg0 _) (Real.sqrt_nonneg _)
    · rw [Set.indicator_of_notMem ht]
  have hqc : HasCompactSupport q := HasCompactSupport.intro hKe hzero
  have hqs : ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases ht : y ∈ e.target
    · have hnb : e.target ∈ nhds y := e.open_target.mem_nhds ht
      have h1 : ContDiffAt ℝ (↑(⊤ : ENat) : WithTop ENat) (fun y => g (e.symm y) * J y) y :=
        (hg.contDiffAt.comp y (he.contDiffAt hnb)).mul (hJ.contDiffAt hnb)
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hnb] with z hz
      simp only [hqdef, localTransportAmplitude, Set.indicator_of_mem hz]
    · have hnb : (e '' tsupport g)ᶜ ∈ nhds y :=
        hKe.isClosed.isOpen_compl.mem_nhds (fun h => ht (hKt h))
      refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnb] with z hz
      exact hzero z hz
  -- measure identity
  have hmeas_g : Measurable (fun x => ENNReal.ofReal (g x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hg.continuous.pow 2).measurable
  have hae : LocalBranchMeasure.extendedBranch e 0 =ᵐ[densityMeasure (fun x => g x ^ 2)] e := by
    rw [densityMeasure, Filter.EventuallyEq, ae_withDensity_iff hmeas_g]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hgx : g x ≠ 0 := by
      intro h0; apply hx; simp [h0]
    exact LocalBranchMeasure.extendedBranch_apply_of_mem e 0 (hgs (subset_tsupport _ hgx))
  have hmap : Measure.map (LocalBranchMeasure.extendedBranch e 0) (densityMeasure (fun x => g x ^ 2)) =
      densityMeasure (fun y => q y ^ 2) := by
    rw [Measure.map_congr hae]
    exact h41_msd e g hgs D hD
  have hextm : Measurable (LocalBranchMeasure.extendedBranch e (0 : E3)) := by
    have : LocalBranchMeasure.extendedBranch e (0 : E3) = e.source.piecewise e (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ e.source
      · rw [LocalBranchMeasure.extendedBranch_apply_of_mem e 0 hx, Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        simp [LocalBranchMeasure.extendedBranch, hx]
    rw [this]
    exact ContinuousOn.measurable_piecewise e.continuousOn continuousOn_const e.open_source.measurableSet
  have hcg : HasCompactSupport (fun x : E3 => g x ^ 2) := by
    exact HasCompactSupport.intro hgc (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hcq : HasCompactSupport (fun x : E3 => q x ^ 2) := by
    exact HasCompactSupport.intro hqc (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hcontg : Continuous (fun x : E3 => g x ^ 2) := hg.continuous.pow 2
  have hcontq : Continuous (fun x : E3 => q x ^ 2) := hqs.continuous.pow 2
  have hint_g : Integrable (fun x : E3 => g x ^ 2) := hcontg.integrable_of_hasCompactSupport hcg
  have hint_q : Integrable (fun x : E3 => q x ^ 2) := hcontq.integrable_of_hasCompactSupport hcq
  have hM := congrArg (fun μ : Measure E3 => μ Set.univ) hmap
  simp only [Measure.map_apply hextm MeasurableSet.univ, Set.preimage_univ, densityMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hM
  rw [← ofReal_integral_eq_lintegral_ofReal hint_g (Filter.Eventually.of_forall fun x => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal hint_q (Filter.Eventually.of_forall fun x => by positivity),
    hmass, ENNReal.ofReal_one] at hM
  have hq1 : (∫ y : E3, q y ^ 2) = 1 := (ENNReal.ofReal_eq_one.mp hM.symm)
  exact ⟨q, hq0, hqs, hqc, hsupp, hq1, hmap⟩

theorem solution
    (c : E3) {r : ℝ} (hr : 0 < r)
    (e : Fin 4 → OpenPartialHomeomorph E3 E3)
    (hsource : ∀ i, Metric.ball c r ⊆ (e i).source)
    (hdisj : Pairwise (fun i j => Disjoint
      (componentRegion (Metric.ball c r) e i) (componentRegion (Metric.ball c r) e j)))
    (he : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat) (e i).symm (e i).target)
    (D : Fin 4 → E3 → E3 →L[ℝ] E3)
    (hD : ∀ i y, y ∈ (e i).target → HasFDerivAt (e i).symm (D i y) y)
    (hJ : ∀ i, ContDiffOn ℝ (↑(⊤ : ENat) : WithTop ENat)
      (fun y => Real.sqrt |(D i y).det|) (e i).target) :
    ∃ (g : E3 → ℝ) (q : Fin 4 → E3 → ℝ),
      NormalizedAmplitude g ∧ tsupport g ⊆ Metric.ball c r ∧
      (∀ i, NormalizedAmplitude (q i) ∧ tsupport (q i) ⊆ e i '' Metric.ball c r) ∧
      IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) ∧
      IsSmoothCompactProbabilityDensity (marginalDensity g q) ∧
      densityMeasure (marginalDensity g q) =
        (1 / 3 : ℝ≥0∞) • densityMeasure (fun x => g x ^ 2) +
        ∑ i : Fin 4, (1 / 6 : ℝ≥0∞) •
          Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
            (densityMeasure (fun x => g x ^ 2)) := by
  obtain ⟨g, hg0, hgs, hgc, hgt, hgm⟩ := h41_bump c hr
  have hsrc : ∀ i, tsupport g ⊆ (e i).source := fun i => hgt.trans (hsource i)
  have hq : ∀ i, ∃ q : E3 → ℝ, (∀ y, 0 ≤ q y) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) q ∧ HasCompactSupport q ∧
      tsupport q ⊆ e i '' tsupport g ∧ (∫ y : E3, q y ^ 2) = 1 ∧
      Measure.map (LocalBranchMeasure.extendedBranch (e i) 0)
        (densityMeasure (fun x => g x ^ 2)) = densityMeasure (fun y => q y ^ 2) :=
    fun i => h41_tsa (e i) hg0 hgs hgc (hsrc i) hgm (he i) (D i) (hD i) (hJ i)
  choose q hq0 hqs hqc hqt hqm hqmap using hq
  have hint : Integrable (fun x : E3 => g x ^ 2) :=
    (hgs.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hgc (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))
  have hprob : IsProbabilityMeasure (densityMeasure (fun x => g x ^ 2)) := by
    constructor
    rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
      hgm, ENNReal.ofReal_one]
  have hA : ∀ i : Option (Fin 4), (∀ x, 0 ≤ componentAmplitude g q i x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) (componentAmplitude g q i) ∧
      HasCompactSupport (componentAmplitude g q i) ∧
      (∫ x : E3, componentAmplitude g q i x ^ 2) = 1 ∧
      tsupport (componentAmplitude g q i) ⊆ componentRegion (Metric.ball c r) e i := by
    rintro (_ | i)
    · exact ⟨hg0, hgs, hgc, hgm, hgt⟩
    · exact ⟨hq0 i, hqs i, hqc i, hqm i, (hqt i).trans (Set.image_mono hgt)⟩
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Option (Fin 4))), 0 ≤ componentWeight i := by
    rintro (_ | i) _ <;> norm_num [componentWeight]
  have hwsum : (∑ i ∈ (Finset.univ : Finset (Option (Fin 4))), componentWeight i) = 1 := by
    simp [Fintype.sum_option, componentWeight]; norm_num
  have hdA : ∀ i ∈ (Finset.univ : Finset (Option (Fin 4))), ∀ j ∈ (Finset.univ : Finset (Option (Fin 4))),
      i ≠ j → Disjoint (Function.support (componentAmplitude g q i))
        (Function.support (componentAmplitude g q j)) := fun i _ j _ hij =>
    (hdisj hij).mono (subset_tsupport _ |>.trans (hA i).2.2.2.2) (subset_tsupport _ |>.trans (hA j).2.2.2.2)
  have hdens : IsSmoothCompactProbabilityDensity (marginalDensity g q) :=
    h41_scpd Finset.univ componentWeight (componentAmplitude g q) hw0
      (fun i _ => (hA i).1) (fun i _ => (hA i).2.1) (fun i _ => (hA i).2.2.1) hdA
      (fun i _ => (hA i).2.2.2.1) hwsum
  have hw3 : ENNReal.ofReal (1 / 3) = (1 / 3 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have hw6 : ENNReal.ofReal (1 / 6) = (1 / 6 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  refine ⟨g, q, ⟨hg0, hgs, hgc, hgm⟩, hgt,
    fun i => ⟨⟨hq0 i, hqs i, hqc i, hqm i⟩, (hqt i).trans (Set.image_mono hgt)⟩, hprob, hdens, ?_⟩
  rw [show marginalDensity g q = fun x => ∑ i ∈ (Finset.univ : Finset (Option (Fin 4))),
      componentWeight i * componentAmplitude g q i x ^ 2 from rfl,
    h41_dsw Finset.univ componentWeight (componentAmplitude g q) hw0
      (fun i _ => (hA i).2.1.continuous.measurable), Fintype.sum_option]
  congr 1
  · simp only [componentWeight, componentAmplitude, hw3]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hqmap i]
    simp only [componentWeight, componentAmplitude, hw6]

