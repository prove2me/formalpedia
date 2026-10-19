-- Prove2me | solution 1 for OAI.Problem356.SmoothBranchMarginal.transported_square_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:44:33.204706+00:00
-- url     : https://prove2.me/submissions/7fbf422a-2b75-4b85-bcd3-1c0fbdafb079

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

theorem solution
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

