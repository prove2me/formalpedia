-- Prove2me | solution 1 for Malliavin.isSeparable_of_isWienerGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:18.236702+00:00
-- url     : https://prove2.me/submissions/269049f9-d817-4161-9bc9-99d4f8c15a15

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.mem_symmetricSubmodule


section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
namespace Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
omit mΩ in
private theorem countableProcessMeasurableSpace_countablyGenerated
    (B : ℝ≥0 → Ω → ℝ) :
    @MeasurableSpace.CountablyGenerated Ω (countableProcessMeasurableSpace B) := by
  rw [countableProcessMeasurableSpace, ← MeasurableSpace.comap_process_pi]
  exact MeasurableSpace.CountablyGenerated.comap _
omit mΩ in
private theorem countableProcessMeasurableSpace_le_processMeasurableSpace
    (B : ℝ≥0 → Ω → ℝ) :
    countableProcessMeasurableSpace B ≤ processMeasurableSpace B := by
  rw [countableProcessMeasurableSpace]
  exact iSup_le fun n ↦ le_iSup (fun t : ℝ≥0 ↦
    MeasurableSpace.comap (B t) (borel ℝ)) (TopologicalSpace.denseSeq ℝ≥0 n)
private theorem brownianEvalL2_dist_sq (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ‖brownianEvalL2 hB s - brownianEvalL2 hB t‖ ^ 2 = nndist (s : ℝ) (t : ℝ) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hst := (hB.isGaussianProcess.hasGaussianLaw_sub (s := s) (t := t)).memLp_two
  have hmean : ∫ ω, (B s - B t) ω ∂P = 0 := by
    change ∫ ω, (B s ω - B t ω) ∂P = 0
    rw [integral_sub (hB.integrable_eval s) (hB.integrable_eval t),
      hB.integral_eval, hB.integral_eval, sub_zero]
  have hcov := covariance_eq_sub hst hst
  rw [hmean, mul_zero, sub_zero] at hcov
  rw [@norm_sq_eq_re_inner ℝ, L2.inner_def]
  simp only [RCLike.re_to_real, Real.inner_apply]
  have hcoe : (fun ω ↦ (brownianEvalL2 hB s - brownianEvalL2 hB t) ω *
      (brownianEvalL2 hB s - brownianEvalL2 hB t) ω) =ᵐ[P]
      fun ω ↦ (B s ω - B t ω) * (B s ω - B t ω) := by
    filter_upwards [Lp.coeFn_sub (brownianEvalL2 hB s) (brownianEvalL2 hB t),
      MemLp.coeFn_toLp hs, MemLp.coeFn_toLp ht] with ω hsub hsω htω
    change (brownianEvalL2 hB s - brownianEvalL2 hB t) ω =
      brownianEvalL2 hB s ω - brownianEvalL2 hB t ω at hsub
    change brownianEvalL2 hB s ω = B s ω at hsω
    change brownianEvalL2 hB t ω = B t ω at htω
    rw [hsub, hsω, htω]
  rw [integral_congr_ae hcoe]
  calc
    ∫ ω, (B s ω - B t ω) * (B s ω - B t ω) ∂P =
        cov[B s - B t, B s - B t; P] := hcov.symm
    _ = Var[B s - B t; P] := covariance_self hst.aemeasurable
    _ = Var[id; gaussianReal 0 (nndist (s : ℝ) (t : ℝ))] :=
      (hB.hasLaw_sub s t).variance_eq
    _ = nndist (s : ℝ) (t : ℝ) := variance_id_gaussianReal
private theorem brownianEvalL2_dist (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ‖brownianEvalL2 hB s - brownianEvalL2 hB t‖ =
      Real.sqrt (nndist (s : ℝ) (t : ℝ) : ℝ) := by
  have hsqrt : (Real.sqrt (nndist (s : ℝ) (t : ℝ) : ℝ)) ^ 2 =
      (nndist (s : ℝ) (t : ℝ) : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [brownianEvalL2_dist_sq hB s t,
    norm_nonneg (brownianEvalL2 hB s - brownianEvalL2 hB t),
    Real.sqrt_nonneg (nndist (s : ℝ) (t : ℝ) : ℝ)]
private theorem brownianEvalL2_tendsto (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0} {t : ℝ≥0}
    (hu : Filter.Tendsto u l (𝓝 t)) :
    Filter.Tendsto (fun i ↦ brownianEvalL2 hB (u i)) l (𝓝 (brownianEvalL2 hB t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [brownianEvalL2_dist]
  have hd : Filter.Tendsto
      (fun i ↦ (nndist ((u i : ℝ≥0) : ℝ) (t : ℝ) : ℝ)) l (𝓝 0) := by
    have hc : Continuous fun s : ℝ≥0 ↦ (nndist (s : ℝ) (t : ℝ) : ℝ) := by fun_prop
    convert (hc.tendsto t).comp hu using 1 <;> simp [Function.comp_def]
  convert (Real.continuous_sqrt.tendsto 0).comp hd using 1 <;>
    simp [Function.comp_def]
private theorem exists_denseTimeApprox (t : ℝ≥0) :
    ∃ k : ℕ → ℕ,
      Filter.Tendsto (fun n ↦ TopologicalSpace.denseSeq ℝ≥0 (k n)) Filter.atTop (𝓝 t) := by
  have ht : t ∈ closure (Set.range (TopologicalSpace.denseSeq ℝ≥0)) := by
    rw [(TopologicalSpace.denseRange_denseSeq ℝ≥0).closure_eq]
    exact Set.mem_univ t
  obtain ⟨q, hq, hqt⟩ := mem_closure_iff_seq_limit.mp ht
  choose k hk using hq
  refine ⟨k, ?_⟩
  convert hqt using 1
  funext n
  exact hk n
omit mΩ in
private theorem measurable_denseTime_eval (B : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    @Measurable Ω ℝ (countableProcessMeasurableSpace B) (borel ℝ)
      (B (TopologicalSpace.denseSeq ℝ≥0 n)) := by
  exact Measurable.of_comap_le (le_iSup (fun k : ℕ ↦
    MeasurableSpace.comap (B (TopologicalSpace.denseSeq ℝ≥0 k)) (borel ℝ)) n)
private theorem exists_countableProcess_measurable_ae_eq
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∃ g : Ω → ℝ,
      @Measurable Ω ℝ (countableProcessMeasurableSpace B) (borel ℝ) g ∧ g =ᵐ[P] B t := by
  obtain ⟨k, hk⟩ := exists_denseTimeApprox t
  have hLp := brownianEvalL2_tendsto hB hk
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, _hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  let q : ℕ → ℝ≥0 := fun i ↦ TopologicalSpace.denseSeq ℝ≥0 (k (ns i))
  let g : Ω → ℝ := fun ω ↦ Filter.limsup (fun i ↦ B (q i) ω) Filter.atTop
  refine ⟨g, ?_, ?_⟩
  · exact Measurable.limsup fun i ↦ measurable_denseTime_eval B (k (ns i))
  · have hcoe_seq : ∀ᵐ ω ∂P, ∀ i,
        brownianEvalL2 hB (q i) ω = B (q i) ω :=
      ae_all_iff.mpr fun i ↦
        MemLp.coeFn_toLp (hB.isGaussianProcess.hasGaussianLaw_eval (q i)).memLp_two
    have hcoe_t : brownianEvalL2 hB t =ᵐ[P] B t :=
      MemLp.coeFn_toLp (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    filter_upwards [hae, hcoe_seq, hcoe_t] with ω hlim hseq ht
    have hlim' : Filter.Tendsto (fun i ↦ B (q i) ω) Filter.atTop (𝓝 (B t ω)) := by
      convert hlim using 1
      · funext i
        exact (hseq i).symm
      · exact congrArg (fun x : ℝ ↦ 𝓝 x) ht.symm
    exact hlim'.limsup_eq
private theorem exists_countableProcess_measurableSet_ae_eq
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    {s : Set Ω} (hs : MeasurableSet s) :
    ∃ t : Set Ω, @MeasurableSet Ω (countableProcessMeasurableSpace B) t ∧ s =ᵐ[P] t := by
  let mAE : MeasurableSpace Ω :=
    { MeasurableSet' := fun s ↦
        ∃ t : Set Ω, @MeasurableSet Ω (countableProcessMeasurableSpace B) t ∧ s =ᵐ[P] t
      measurableSet_empty :=
        ⟨∅, @MeasurableSet.empty Ω (countableProcessMeasurableSpace B),
          Filter.EventuallyEq.rfl⟩
      measurableSet_compl := by
        rintro s ⟨t, ht, hst⟩
        exact ⟨tᶜ, ht.compl, hst.compl⟩
      measurableSet_iUnion := by
        intro f hf
        choose g hgm hfg using hf
        refine ⟨⋃ i, g i, @MeasurableSet.iUnion Ω ℕ
          (countableProcessMeasurableSpace B) inferInstance g hgm, ?_⟩
        have hall : ∀ᵐ ω ∂P, ∀ i, ω ∈ f i ↔ ω ∈ g i :=
          ae_all_iff.mpr fun i ↦ (hfg i).mono fun _ h ↦ h.to_iff
        filter_upwards [hall] with ω hω
        change (ω ∈ ⋃ i, f i) = (ω ∈ ⋃ i, g i)
        apply propext
        constructor
        · intro hw
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
          exact Set.mem_iUnion.mpr ⟨i, (hω i).mp hi⟩
        · intro hw
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
          exact Set.mem_iUnion.mpr ⟨i, (hω i).mpr hi⟩ }
  have hcoord (t : ℝ≥0) : @Measurable Ω ℝ mAE (borel ℝ) (B t) := by
    intro u hu
    obtain ⟨g, hg, hgt⟩ :=
      exists_countableProcess_measurable_ae_eq (mΩ := mΩ) hB t
    refine ⟨g ⁻¹' u, hg hu, ?_⟩
    filter_upwards [hgt] with ω hω
    change (B t ω ∈ u) = (g ω ∈ u)
    exact congrArg (· ∈ u) hω.symm
  have hprocess : processMeasurableSpace B ≤ mAE :=
    iSup_le fun t ↦ (hcoord t).comap_le
  have hambient : mΩ ≤ mAE := by
    rw [← hgen]
    exact hprocess
  exact hambient s hs
end Malliavin
end
end

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    MeasureTheory.IsSeparable P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmD : countableProcessMeasurableSpace B ≤ mΩ := by
    rw [← hgen]
    exact countableProcessMeasurableSpace_le_processMeasurableSpace B
  let μD : @Measure Ω (countableProcessMeasurableSpace B) := P.trim hmD
  let _ : @MeasurableSpace.CountablyGenerated Ω (countableProcessMeasurableSpace B) :=
    countableProcessMeasurableSpace_countablyGenerated B
  let _ : IsFiniteMeasure μD := MeasureTheory.isFiniteMeasure_trim hmD
  have hsepD : @MeasureTheory.IsSeparable Ω (countableProcessMeasurableSpace B) μD :=
    @MeasureTheory.isSeparable_of_sigmaFinite Ω (countableProcessMeasurableSpace B)
      μD inferInstance inferInstance
  obtain ⟨A, hAc, hAdense⟩ :=
    @exists_countable_measureDense Ω (countableProcessMeasurableSpace B) μD hsepD
  refine ⟨A, hAc, ?_⟩
  refine
    { measurable := by
        intro u hu
        apply hmD
        exact @Measure.MeasureDense.measurable Ω (countableProcessMeasurableSpace B)
          μD A hAdense u hu
      approx := ?_ }
  intro s hs _ ε hε
  obtain ⟨t, ht, hst⟩ := exists_countableProcess_measurableSet_ae_eq hB hgen hs
  have htfinite : μD t ≠ ∞ := (measure_lt_top μD t).ne
  obtain ⟨u, hu, htu⟩ :=
    @Measure.MeasureDense.approx Ω (countableProcessMeasurableSpace B) μD A
      hAdense t ht htfinite ε hε
  refine ⟨u, hu, ?_⟩
  have huD : @MeasurableSet Ω (countableProcessMeasurableSpace B) u :=
    @Measure.MeasureDense.measurable Ω (countableProcessMeasurableSpace B)
      μD A hAdense u hu
  have hsu : (s ∆ u) =ᵐ[P] (t ∆ u) :=
    hst.symmDiff (Filter.EventuallyEq.rfl : u =ᵐ[P] u)
  have htuD : @MeasurableSet Ω (countableProcessMeasurableSpace B) (t ∆ u) :=
    ht.symmDiff huD
  have htrim : μD (t ∆ u) = P (t ∆ u) := trim_measurableSet_eq hmD htuD
  calc
    P (s ∆ u) = P (t ∆ u) := measure_congr hsu
    _ = μD (t ∆ u) := htrim.symm
    _ < ENNReal.ofReal ε := htu
end Malliavin
