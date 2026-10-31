-- Prove2me | solution 1 for OAI.CAT0Fillings.normalized_extremal_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:11:49.376979+00:00
-- url     : https://prove2.me/submissions/d6e85127-78aa-4262-ba2d-105d8e3d98e7

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_ChartGeometry_euler_chord_contradiction
import Theorems.Thm_OAI_CAT0Fillings_extremal_closed_sobolev
import Theorems.Thm_OAI_CAT0Fillings_extremal_critical_minimizer
import Theorems.Thm_OAI_CAT0Fillings_extremal_euler_powers
import Theorems.Thm_OAI_CAT0Fillings_radial_inequality_of_extremal

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Euclidean
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma omega_gamma {k : ℕ} (hk : 0 < k) :
    omega k = Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2+1) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [omega, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.toReal_ofReal
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ComponentMass
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma tendsto_integral_abs_of_l1 {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) {f : ℕ → X → ℝ} {b : X → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hb : Integrable b μ)
    (hlim : Tendsto (fun j => ∫ x, |f j x-b x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, |f j x| ∂ν) atTop (𝓝 (∫ x, |b x| ∂ν)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hlim
  rw [Real.dist_eq,←integral_sub ((hf j).mono_measure hν).abs (hb.mono_measure hν).abs]
  calc |∫ x, |f j x|-|b x| ∂ν| ≤ ∫ x, abs (|f j x|-|b x|) ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => |f j x|-|b x|)
    _ ≤ ∫ x, |f j x-b x| ∂ν :=
        integral_mono_ae (((hf j).mono_measure hν).abs.sub (hb.mono_measure hν).abs).abs
          (((hf j).mono_measure hν).sub (hb.mono_measure hν)).abs
          (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
    _ ≤ ∫ x, |f j x-b x| ∂μ :=
        integral_mono_measure hν (Eventually.of_forall fun _ => abs_nonneg _)
          ((hf j).sub hb).abs
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

section ComponentControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]
  {Z : ℕ → Set X}

lemma component_approximation_bound (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i) (i : ℕ)
    {f b : X → ℝ} (hf : BoundedLip f) (hb : BoundedLip b)
    {π : Fin k → X → ℝ} (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |T f π - S i b π| ≤ ∫ x, |f x - (Z i).indicator b x| ∂Measure.sum μ := by
  classical
  have hfi := BorelCoefficients.integrable_boundedLip (Measure.sum μ) hf
  have hbi := (BorelCoefficients.integrable_boundedLip (Measure.sum μ) hb).indicator (hZ i)
  let d : ℕ → ℝ := fun j => S j f π - if j = i then S i b π else 0
  have hbd (j : ℕ) : |d j| ≤ ∫ x, |f x-(Z i).indicator b x| ∂μ j := by
    by_cases hji : j = i
    · subst j
      have heq : S i (fun x => f x - b x) π = S i f π - S i b π := by
        simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
          (hS i).linearFirst f b π 1 (-1) hf hb (fun l => ⟨1,hπ l⟩)
      have hbound := hμ i (fun x => f x-b x) π (by simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hb.const_mul (-1))) hπ
      rw [heq] at hbound
      change |S i f π - if i = i then S i b π else 0| ≤ _
      rw [ite_eq_left rfl]
      apply hbound.trans_eq
      apply integral_congr_ae
      filter_upwards [hc i] with x hx
      rw [indicator_of_mem hx]
    · have hbound := hμ j f π hf hπ
      change |S j f π - if j = i then S i b π else 0| ≤ _
      rw [ite_eq_right hji,sub_zero]
      apply hbound.trans_eq
      apply integral_congr_ae
      filter_upwards [hc j] with x hx
      have hxi : x ∉ Z i := fun hxi => Set.disjoint_left.mp (hd hji) hx hxi
      rw [indicator_of_notMem hxi,sub_zero]
  have heint : Integrable (fun x => |f x-(Z i).indicator b x|) (Measure.sum μ) :=
    (hfi.sub hbi).abs
  have he : Summable (fun j => ∫ x, |f x-(Z i).indicator b x| ∂μ j) := by
    simpa only [Real.norm_eq_abs,abs_abs] using heint.summable_integral
  have hdS : Summable d := he.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using hbd j)
  have hfS : Summable (fun j => S j f π) := by
    have hfs : Summable (fun j => ∫ x, |f x| ∂μ j) := by
      simpa only [Real.norm_eq_abs,abs_abs] using hfi.abs.summable_integral
    exact hfs.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using hμ j f π hf hπ)
  have hsum : ∑' j, d j = T f π - S i b π := by
    rw [hT f π]
    dsimp only [d]
    rw [hfS.tsum_sub (hasSum_ite_eq i (S i b π)).summable,tsum_ite_eq]
  rw [←hsum,integral_sum_measure heint]
  calc |∑' j, d j| ≤ ∑' j, |d j| := by
        simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm (f := d) hdS.norm)
    _ ≤ ∑' j, ∫ x, |f x-(Z i).indicator b x| ∂μ j := hdS.abs.tsum_le_tsum hbd he

lemma controls_component_restrict (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν) (i : ℕ) :
    Controls (S i) (ν.restrict (Z i)) := by
  intro b π hb hπ
  let η := ν + Measure.sum μ
  have hbη : Integrable ((Z i).indicator b) η :=
    (BorelCoefficients.integrable_boundedLip η hb).indicator (hZ i)
  obtain ⟨f,hf⟩ := BorelCoefficients.exists_lipschitz_approximation η hbη
  have hfi (j : ℕ) : Integrable (f j).val η :=
    BorelCoefficients.integrable_boundedLip η (f j).property
  have hleμ : Measure.sum μ ≤ η := Measure.le_add_left le_rfl
  have hleν : ν ≤ η := Measure.le_add_right le_rfl
  have hlim : Tendsto (fun j => T (f j).val π) atTop (𝓝 (S i b π)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq]
    apply (component_approximation_bound hS hμ hT hZ hd hc i (f j).property hb hπ).trans
    exact integral_mono_measure hleμ (Eventually.of_forall fun _ => abs_nonneg _)
      ((hfi j).sub hbη).abs
  have hlimν := tendsto_integral_abs_of_l1 hleν hfi hbη hf
  have hle := le_of_tendsto_of_tendsto hlim.abs hlimν
    (Eventually.of_forall fun j => hν _ π (f j).property hπ)
  apply hle.trans_eq
  rw [←integral_indicator (hZ i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ Z i <;> simp [hx]

end ComponentControls
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma sum_measure_le_of_component_minimal
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
    {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]
    {Z : ℕ → Set X}
    (hS : ∀ i, IsMetricCurrent (S i)) (hμ : ∀ i, Controls (S i) (μ i))
    (hmin : ∀ i (ν : Measure X), IsFiniteMeasure ν → Controls (S i) ν → μ i ≤ ν)
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν) : Measure.sum μ ≤ ν := by
  have hle (i) : μ i ≤ ν.restrict (Z i) :=
    hmin i _ inferInstance (controls_component_restrict hS hμ hT hZ hd hc hν i)
  have hsum : Measure.sum μ ≤ Measure.sum (fun i => ν.restrict (Z i)) := by
    apply Measure.le_iff.mpr
    intro B hB
    simp only [Measure.sum_apply _ hB]
    exact ENNReal.tsum_le_tsum (fun i => hle i B)
  rw [←Measure.restrict_iUnion hd hZ] at hsum
  exact hsum.trans Measure.restrict_le_self

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_RectifiableMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma majorantMeasure_ae_image (J : Euc k → ℝ) :
    ∀ᵐ x ∂C.majorantMeasure J, x ∈ C.image := by
  rw [majorantMeasure,densityPush]
  apply (ae_map_iff C.measurable_paramExtended.aemeasurable C.measurableSet_image).mpr
  have hmem := (withDensity_absolutelyContinuous (volume.restrict C.domain)
    (fun z => ENNReal.ofReal (|(C.multiplicity z : ℝ)| * J z))).ae_le (ae_restrict_mem C.borel)
  filter_upwards [hmem] with z hz
  exact ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩

end IntegerChart

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_SumControls
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

section SumControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]

omit [CompactSpace X] in
lemma controls_sum_general (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π) : Controls T (Measure.sum μ) := by
  intro b π hb hπ
  have hbi : Integrable (fun x => |b x|) (Measure.sum μ) :=
    (hb.toBoundedContinuous.integrable (Measure.sum μ)).abs
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbi.summable_integral
  have hsa : Summable (fun i => S i b π) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hμ i b π hb hπ)
  rw [hT b π,integral_sum_measure hbi]
  calc
    |∑' i, S i b π| ≤ ∑' i, |S i b π| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => S i b π) hsa.norm)
    _ ≤ ∑' i, ∫ x, |b x| ∂μ i := hsa.abs.tsum_le_tsum (fun i => hμ i b π hb hπ) hs

end SumControls

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MassComparison
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix CurrentOperations
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
theorem mass_eq_integral_majorant (hC : IsMetricCurrent C.action) {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z)
      (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hcontrol : Controls C.action (C.majorantMeasure J))
    (hmin : ∀ ν : Measure X, IsFiniteMeasure ν → Controls C.action ν →
      C.majorantMeasure J ≤ ν) :
    mass C.action = ∫ z, |(C.multiplicity z : ℝ)| * J z ∂volume.restrict C.domain := by
  have hfin : IsFiniteMeasure (C.majorantMeasure J) := densityPush_finite _ _ hρ
  have hνeq : (C.majorantMeasure J).real univ =
      ∫ z, |(C.multiplicity z : ℝ)| * J z ∂volume.restrict C.domain := by
    have hh := integral_densityPush (volume.restrict C.domain)
      C.measurable_paramExtended hρ
      (hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz) (continuous_const (y := (1:ℝ)))
    simpa only [majorantMeasure,integral_const,smul_eq_mul,mul_one] using hh
  rw [←hνeq]
  apply le_antisymm (mass_le_measure hfin hcontrol)
  obtain ⟨ν,hν,hνc,heq⟩ := hC.exists_controls_mass_eq
  rw [heq]
  exact ENNReal.toReal_mono (by let := hν; exact measure_ne_top ν univ)
    (hmin ν hν hνc univ)

end IntegerChart
end CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Current
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem exists_chartGeometry {T : Functional X k}
    (hX : IsCAT0 X) (hT : IsMetricCurrent T) (hr : IntegerRectifiable T) :
    Nonempty (ChartGeometry hT) := by
  classical
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hr
  choose P hPm hP hρ hfin hcontrol hmin hfield using
    fun i => (C i).exists_exact_quadratic_mass hX (hC i)
  choose p hPeq hpm hp using hfield
  simp only [hPeq] at hρ hfin hcontrol hmin
  let J (i : ℕ) (z : Euc k) := Real.sqrt
    (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
  have hmass (i : ℕ) : mass (C i).action =
      ∫ z, |((C i).multiplicity z : ℝ)| *J i z ∂volume.restrict (C i).domain :=
    (C i).mass_eq_integral_majorant (hC i) (hρ i)
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _) (hcontrol i) (hmin i)
  let μ (i : ℕ) : Measure X := (C i).majorantMeasure (J i)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := hfin
  let := hμfin
  have htot (i : ℕ) : (μ i).real univ = mass (C i).action := by
    have heqm : MassMeasure.currentMassMeasure (hC i) = μ i := by
      apply le_antisymm (MassMeasure.currentMassMeasure_le (hC i) (hcontrol i))
      exact hmin i _ inferInstance (MassMeasure.currentMassMeasure_controls (hC i))
    rw [←heqm]
    exact MassMeasure.currentMassMeasure_total _
  have hμsum : Summable (fun i => (μ i).real univ) := by simpa only [htot] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  have hmeasure : MassMeasure.currentMassMeasure hT = Measure.sum μ := by
    apply le_antisymm
    · exact MassMeasure.currentMassMeasure_le hT (controls_sum_general hcontrol heq)
    · exact sum_measure_le_of_component_minimal hC hcontrol hmin heq
        (fun i => (C i).measurableSet_image) hdis
        (fun i => (C i).majorantMeasure_ae_image _) (MassMeasure.currentMassMeasure_controls hT)
  have htotal : mass T = ∑' i, mass (C i).action := by
    rw [←MassMeasure.currentMassMeasure_total hT,hmeasure]
    rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.tsum_toReal_eq (fun i => measure_ne_top (μ i) univ)]
    exact tsum_congr htot
  exact ⟨⟨C,p,hdis,hsum,heq,hpm,hp,hρ,hmass,hmeasure,htotal,hC,hcontrol⟩⟩

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Multiplier
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_chain {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) :
    q.gradientFunction (F ∘ u) =ᵐ[q.atlasMeasure]
      (fun w => F' (u (q.atlasParam w)) • q.gradientFunction u w) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨f,hf,hef⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (F ∘ u)) (F ∘ f) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz,Function.comp_apply]
    rw [←hef hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hf hef,
    ae_fderivWithin_eq_fderiv_extension volume C.borel (hF.comp hf) hecomp,
    hf.ae_differentiableAt.filter_mono ae_restrict_le,ae_restrict_mem C.borel] with z hu hcomp hdz hz
  change z ∈ C.domain at hz
  change q.normalizedCovector i (F ∘ u) z =
    F' (u (C.paramExtended z)) • q.normalizedCovector i u z
  have hname : f z = u (C.paramExtended z) := by
    rw [←hef hz]
    simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz]
  have hd := (hdF (f z)).comp_hasFDerivAt z hdz.hasFDerivAt
  dsimp only [normalizedCovector,covector]
  rw [hcomp,hd.fderiv,hu,hname]
  have he : differentialRow (F' (u (C.paramExtended z)) • fderiv ℝ f z) =
      F' (u (C.paramExtended z)) • differentialRow (fderiv ℝ f z) := rfl
  rw [he,Matrix.mulVec_smul,WithLp.toLp_smul]

lemma gradient_chain_ae {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) :
    q.gradient (hF.comp hu) =ᵐ[q.atlasMeasure]
      (fun w => F' (u (q.atlasParam w)) • q.gradient hu w) := by
  filter_upwards [(q.memLp_gradientFunction (hF.comp hu)).coeFn_toLp,
    (q.memLp_gradientFunction hu).coeFn_toLp,q.gradientFunction_chain hu hF hdF] with w h1 h2 h3
  exact h1.trans (h3.trans (congrArg (F' (u (q.atlasParam w)) • ·) h2.symm))

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma l2_norm_sq (g : Lp E 2 μ) : ‖g‖^2 = ∫ x, ‖g x‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma l2_tendsto_zero_of_bound (f : ℕ → Lp E 2 μ) (g : α → ℝ)
    (hg : Integrable (fun x => (g x)^2) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ g x)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have hh : Tendsto (fun j => ∫ x, ‖f j x‖^2 ∂μ) atTop (𝓝 (∫ _ : α, (0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => g x^2)
      (fun j => (Lp.aestronglyMeasurable (f j)).norm.pow 2) hg
    · intro j
      filter_upwards [hb j] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx
    · filter_upwards [hl] with x hx
      simpa only [Pi.pow_apply,norm_zero,zero_pow (by decide : 2 ≠ 0)] using hx.norm.pow 2
  simp only [integral_zero,←l2_norm_sq] at hh
  have hn := hh.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

lemma mulLp_ae {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g : Lp E 2 μ) :
    mulLp hb hC g =ᵐ[μ] (fun x => b x • g x) := (memLp_smul_bounded hb hC g).coeFn_toLp

lemma mulLp_sub_bound {b : α → ℝ} (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, |b x| ≤ C) (g h : Lp E 2 μ) :
    ‖mulLp hb hC g-mulLp hb hC h‖ ≤ C*‖g-h‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (mulLp hb hC g) (mulLp hb hC h),mulLp_ae hb hC g,
    mulLp_ae hb hC h,Lp.coeFn_sub g h,hC] with x hs hg hh hd hCx
  rw [hs,hd,Pi.sub_apply,hg,hh,←smul_sub,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hCx (norm_nonneg _)

lemma mulLp_tendsto {b : ℕ → α → ℝ} {c : α → ℝ}
    (hb : ∀ j, AEStronglyMeasurable (b j) μ) (hc : AEStronglyMeasurable c μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbC : ∀ j, ∀ᵐ x ∂μ, |b j x| ≤ C) (hcC : ∀ᵐ x ∂μ, |c x| ≤ C)
    (hbc : ∀ᵐ x ∂μ, Tendsto (fun j => b j x) atTop (𝓝 (c x)))
    {g : ℕ → Lp E 2 μ} {h : Lp E 2 μ} (hgh : Tendsto g atTop (𝓝 h)) :
    Tendsto (fun j => mulLp (hb j) (hbC j) (g j)) atTop (𝓝 (mulLp hc hcC h)) := by
  have hfixed : Tendsto (fun j => mulLp (hb j) (hbC j) h-mulLp hc hcC h) atTop (𝓝 0) := by
    apply l2_tendsto_zero_of_bound _ (fun x => 2*C*‖h x‖)
    · have hi := (Lp.memLp h).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
      convert hi.const_mul ((2*C)^2) using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      ring
    · intro j
      filter_upwards [Lp.coeFn_sub (mulLp (hb j) (hbC j) h) (mulLp hc hcC h),
        mulLp_ae (hb j) (hbC j) h,mulLp_ae hc hcC h,hbC j,hcC] with x hs hb hc hbC hcC
      rw [hs,Pi.sub_apply,hb,hc,←sub_smul,norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((abs_sub (b j x) (c x)).trans (by linarith)) (norm_nonneg _)
    · have hall : ∀ᵐ x ∂μ, ∀ j, (mulLp (hb j) (hbC j) h-mulLp hc hcC h) x =
          (b j x-c x) • h x := by
        apply ae_all_iff.mpr
        intro j
        filter_upwards [Lp.coeFn_sub (mulLp (hb j) (hbC j) h) (mulLp hc hcC h),
          mulLp_ae (hb j) (hbC j) h,mulLp_ae hc hcC h] with x hs hb hc
        rw [hs,Pi.sub_apply,hb,hc,sub_smul]
      filter_upwards [hall,hbc] with x he hx
      simp_rw [he]
      simpa only [sub_self,zero_smul] using (hx.sub_const (c x)).smul_const (h x)
  have hpert : Tendsto (fun j => mulLp (hb j) (hbC j) (g j)-mulLp (hb j) (hbC j) h)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun j => mulLp_sub_bound (hb j) (hbC j) (g j) h)
    simpa only [Real.norm_of_nonneg hC,sub_self,norm_zero,mul_zero] using
      ((hgh.sub_const h).norm).const_mul ‖C‖
  have hh := hpert.add hfixed
  simp only [sub_add_sub_cancel,add_zero] at hh
  have hf := hh.add_const (mulLp hc hcC h)
  simpa only [sub_add_cancel,zero_add] using hf

end CAT0Fillings.ClosedCalculus
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Completion
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGraph_isClosed : IsClosed (q.closedGraph : Set q.GraphAmbient) :=
  q.lipschitzGraph.isClosed_topologicalClosure

instance instCompleteSpaceSubtypeGraphAmbientMemSubmoduleRealSobolev : CompleteSpace q.Sobolev := q.closedGraph_isClosed.completeSpace_coe

lemma exists_lipschitz_approximants (P : q.Sobolev) :
    ∃ (u : ℕ → X → ℝ) (K : ℕ → ℝ≥0) (hu : ∀ j, LipschitzWith (K j) (u j)),
      Tendsto (fun j => q.graphPoint (hu j)) atTop (𝓝 (P : q.GraphAmbient)) := by
  have hp : (P : q.GraphAmbient) ∈ closure (q.lipschitzGraph : Set q.GraphAmbient) := P.property
  obtain ⟨p,hp,hlim⟩ := mem_closure_iff_seq_limit.mp hp
  choose u K hu he using hp
  refine ⟨u,K,hu,?_⟩
  have heq : p = fun j => q.graphPoint (hu j) := funext he
  rw [←heq]
  exact hlim

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGradient_closed (u : Lp ℝ 2 (MassMeasure.currentMassMeasure hT))
    (G : Lp (Euc (k+1)) 2 q.atlasMeasure) (P : ℕ → q.Sobolev)
    (hu : Tendsto (fun j => q.inclusion (P j)) atTop (𝓝 u))
    (hG : Tendsto (fun j => q.closedGradient (P j)) atTop (𝓝 G)) :
    ∃ Q : q.Sobolev, q.inclusion Q = u ∧ q.closedGradient Q = G := by
  have hpair := hu.prodMk_nhds hG
  have hh := ((WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) (Lp (Euc (k+1)) 2 q.atlasMeasure)).symm.continuous.tendsto (u,G)).comp hpair
  have hh' : Tendsto (fun j => (P j : q.GraphAmbient)) atTop
      (𝓝 (WithLp.toLp 2 (u,G))) := hh
  have hm : WithLp.toLp 2 (u,G) ∈ q.closedGraph :=
    q.closedGraph_isClosed.mem_of_tendsto hh' (Eventually.of_forall fun j => (P j).property)
  exact ⟨⟨_,hm⟩,rfl,rfl⟩

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_CriticalNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma lpNorm_sq_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {p : ℝ} (hp : 0 < p) (hf : AEStronglyMeasurable f μ) :
    lpNorm f (ENNReal.ofReal p) μ ^ 2 = (∫ x, |f x|^p ∂μ)^(2/p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs]
  rw [←Real.rpow_mul_natCast (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) ]
  congr 1
  simp only [Nat.cast_ofNat]
  ring

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory ENNReal
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma lpNorm_congr_ae {f g : α → ℝ} (h : f =ᵐ[μ] g) (p : ℝ≥0∞) :
    lpNorm f p μ = lpNorm g p μ := by
  unfold lpNorm
  rw [eLpNorm_congr_ae h]
  by_cases hf : AEStronglyMeasurable f μ
  · rw [if_pos hf, if_pos (hf.congr h)]
  · rw [if_neg hf, if_neg (fun hg => hf (hg.congr h.symm))]

lemma criticalNorm_smul (I : H →L[ℝ] Lp ℝ 2 μ) (p c : ℝ) (u : H) :
    criticalNorm I p (c • u) = |c| *criticalNorm I p u := by
  dsimp [criticalNorm]
  rw [map_smul,lpNorm_congr_ae (Lp.coeFn_smul c (I u)) _,lpNorm_const_smul]
  rfl

lemma criticalNorm_sq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalNorm I p u ^ 2 = criticalMass I p u ^ (2/p) :=
  lpNorm_sq_eq_integral hp (Lp.aestronglyMeasurable _)

lemma criticalMass_eq (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 0 < p) (u : H) :
    criticalMass I p u = criticalNorm I p u ^ p := by
  dsimp [criticalNorm,criticalMass]
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ofReal_ne_top (Lp.aestronglyMeasurable _)]
  simp only [toReal_ofReal hp.le,Real.norm_eq_abs]
  exact (Real.rpow_inv_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) hp.ne').symm

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma composeValue_ae {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (f : Lp ℝ 2 (MassMeasure.currentMassMeasure hT)) :
    q.composeValue hF f =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => F (f x)) := by
  filter_upwards [Lp.coeFn_add ((hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f)
    (value (hT := hT) (LipschitzWith.const (F 0))),
    (hF.sub (LipschitzWith.const (F 0))).coeFn_compLp (by simp) f,
    ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (F 0))).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x ha hb hc
  rw [composeValue,constant,q.inclusion_lipSobolev,ha]
  change ((hF.sub (LipschitzWith.const (F 0))).compLp (by simp) f) x + (value (hT := hT) (LipschitzWith.const (F 0))) x = _
  change (value (hT := hT) (LipschitzWith.const (F 0))) x = F 0 at hc
  rw [hb,hc]
  simp only [Function.comp_apply,sub_add_cancel]

lemma continuous_composeValue {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F) :
    Continuous (q.composeValue hF) :=
  ((hF.sub (LipschitzWith.const (F 0))).continuous_compLp (by simp)).add continuous_const

lemma composeValue_value {F : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.composeValue hF (value hu) = value (hF.comp hu) := by
  apply Lp.ext
  filter_upwards [q.composeValue_ae hF (value hu),
    ((Foundations.boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp,
    ((Foundations.boundedLip_of_lipschitz (hF.comp hu)).memLp
      (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x ha hb hc
  exact ha.trans ((congrArg F hb).trans hc.symm)

lemma closed_chain {F F' : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hdF : ∀ t, HasDerivAt F (F' t) t) (hcF : Continuous F')
    {C : ℝ} (hC : 0 ≤ C) (hbF : ∀ t, |F' t| ≤ C) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => F' ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  obtain ⟨u,K,hu,hl⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hl
  change Tendsto (fun j => value (hu j)) atTop (𝓝 (q.inclusion P)) at hv
  change Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 (q.closedGradient P)) at hg
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hnames : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, ∀ j,
      (value (hT := hT) (hu (s j))) x = u (s j) x := by
    apply ae_all_iff.mpr
    intro j
    exact ((Foundations.boundedLip_of_lipschitz (hu (s j))).memLp 2).coeFn_toLp
  have hae' : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT,
      Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x)) := by
    filter_upwards [hae,hnames] with x hx he
    simpa only [he] using hx
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := F' (u (s j) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := F' ((q.inclusion P) (q.atlasParam w))
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure :=
    (hcF.measurable.comp ((hu (s j)).continuous.measurable.comp q.measurable_atlasParam)).aestronglyMeasurable
  have hc : AEStronglyMeasurable c q.atlasMeasure :=
    hcF.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving)
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun w => hbF _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun w => hbF _
  have hbc : ∀ᵐ w ∂q.atlasMeasure, Tendsto (fun j => b j w) atTop (𝓝 (c w)) := by
    have ha : ∀ᵐ w ∂q.atlasMeasure,
        Tendsto (fun j => u (s j) (q.atlasParam w)) atTop (𝓝 ((q.inclusion P) (q.atlasParam w))) := by
      apply ae_of_ae_map (μ := q.atlasMeasure) (p := fun x =>
        Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x))) q.measurable_atlasParam.aemeasurable
      rwa [q.map_atlasMeasure]
    filter_upwards [ha] with w hw
    exact (hcF.tendsto _).comp hw
  have hgl := ClosedCalculus.mulLp_tendsto hb hc hC hbC hcC hbc (hg.comp hs.tendsto_atTop)
  have he (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.gradient (hu (s j))) =
      q.gradient (hF.comp (hu (s j))) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (q.gradient_chain_ae (hu (s j)) hF hdF).symm
  simp only [Function.comp_apply,he] at hgl
  have hvl := (q.continuous_composeValue hF).tendsto (q.inclusion P) |>.comp (hv.comp hs.tendsto_atTop)
  simp only [Function.comp_def,q.composeValue_value] at hvl
  obtain ⟨Q,hQ,hG⟩ := q.closedGradient_closed (q.composeValue hF (q.inclusion P))
    (ClosedCalculus.mulLp hc hcC (q.closedGradient P))
    (fun j => q.lipSobolev (hF.comp (hu (s j)))) hvl hgl
  refine ⟨Q,?_,?_⟩
  · rw [hQ]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_ClosedLevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_uniform {F D : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C) (hbD : ∀ t, |D t| ≤ C)
    (Fj Dj : ℕ → ℝ → ℝ) (K : ℕ → ℝ≥0)
    (hFj : ∀ j, LipschitzWith (K j) (Fj j))
    (hdj : ∀ j t, HasDerivAt (Fj j) (Dj j t) t)
    (hcj : ∀ j, Continuous (Dj j)) (hbj : ∀ j t, |Dj j t| ≤ C)
    (hdlim : ∀ t, Tendsto (fun j => Dj j t) atTop (𝓝 (D t)))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ j t, |Fj j t-F t| ≤ a j) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  choose Q hQ hG using (fun j => q.closed_chain (hFj j) (hdj j) (hcj j) hC (hbj j) P)
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := Dj j ((q.inclusion P) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := D ((q.inclusion P) (q.atlasParam w))
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure := (hcj j).comp_aestronglyMeasurable hpm
  have hc : AEStronglyMeasurable c q.atlasMeasure := (hD.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun _ => hbj j _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun _ => hbD _
  have hgl := ClosedCalculus.mulLp_tendsto hb hc hC hbC hcC
    (Eventually.of_forall fun point => hdlim ((q.inclusion P) (q.atlasParam point)))
    (tendsto_const_nhds (x := q.closedGradient P))
  have heG (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.closedGradient P) = q.closedGradient (Q j) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (hG j).symm
  simp only [heG] at hgl
  let V := q.composeValue hF (q.inclusion P)
  have hv : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (g := fun j => a j*‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖)
    · intro j
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (q.inclusion (Q j)) V,hQ j,q.composeValue_ae hF (q.inclusion P),
        ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (1:ℝ))).memLp
          (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x hs hq hv h1
      change (value (hT := hT) (LipschitzWith.const (1:ℝ)) : X → ℝ) x = 1 at h1
      rw [hs,Pi.sub_apply,hq,hv,h1,Real.norm_eq_abs,norm_one,mul_one]
      exact he j _
    · simpa only [zero_mul] using ha.mul_const ‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V (ClosedCalculus.mulLp hc hcC (q.closedGradient P)) Q hv hgl
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hRG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_CriticalEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric TopologicalSpace
open scoped Topology

namespace CAT0Fillings.AnalyticMinimizer
variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F] in
lemma energy_smul [CompleteSpace H] [SeparableSpace H] [CompleteSpace E] [CompleteSpace F]
    (I : H →L[ℝ] E) (G : H →L[ℝ] F) (A B c : ℝ) (u : H) :
    energy I G A B (c • u) = c^2*energy I G A B u := by
  simp only [energy,map_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_AbsoluteValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

lemma absApprox_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (absApprox ε) (absApproxDeriv ε t) t := by
  have hh : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hd := (((hasDerivAt_id t).pow 2).add_const (ε^2)).sqrt hh.ne'
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp [absApproxDeriv]
    norm_num
    ring

lemma absApproxDeriv_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |absApproxDeriv ε t| ≤ 1 := by
  have hh : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  dsimp [absApproxDeriv]
  rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_one (Real.sqrt_pos.mpr hh)).mpr
  rw [←Real.sqrt_sq_eq_abs t]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

lemma absApprox_lipschitz {ε : ℝ} (hε : 0 < ε) : LipschitzWith 1 (absApprox ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (absApprox_hasDerivAt hε t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_one,(absApprox_hasDerivAt hε t).deriv,Real.norm_eq_abs]
  exact absApproxDeriv_bound hε t

lemma continuous_absApproxDeriv {ε : ℝ} (hε : 0 < ε) : Continuous (absApproxDeriv ε) := by
  change Continuous (fun t : ℝ => t / Real.sqrt (t^2+ε^2))
  apply continuous_id.div (Real.continuous_sqrt.comp (continuous_id.pow 2 |>.add continuous_const))
  intro t
  exact (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))).ne'

lemma absApprox_error {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) : abs (absApprox ε t-|t|) ≤ ε := by
  have hl : |t| ≤ absApprox ε t := by
    rw [←Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  have hu : absApprox ε t ≤ |t|+ε := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [add_sq,sq_abs]
    nlinarith [abs_nonneg t]
  linarith

lemma absApproxDeriv_tendsto {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hepos : ∀ j, 0 < e j) (t : ℝ) :
    Tendsto (fun j => absApproxDeriv (e j) t) atTop (𝓝 (t / |t|)) := by
  by_cases ht : t = 0
  · subst t
    rw [zero_div]
    apply tendsto_const_nhds.congr
    intro index
    dsimp [absApproxDeriv]
    rw [zero_pow (by decide : 2 ≠ 0),zero_add,Real.sqrt_sq (hepos index).le,zero_div]
  have hab : 0 < |t| := abs_pos.mpr ht
  have hh := (tendsto_const_nhds (x := t) (f := (atTop : Filter ℕ))).div ((tendsto_const_nhds.add (he.pow 2)).sqrt)
    (show Real.sqrt (t^2+(0:ℝ)^2) ≠ 0 by simpa only [zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] using hab.ne')
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs] at hh
  exact hh

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_abs (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => |(q.inclusion P) x|) ∧
      ‖q.inclusion Q‖ = ‖q.inclusion P‖ ∧
      ‖q.closedGradient Q‖ ≤ ‖q.closedGradient P‖ := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hepos (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (t : ℝ) : abs (t/|t|) ≤ 1 := by
    rw [abs_div,abs_abs]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_self (abs_pos.mpr ht).ne']
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_uniform (F := abs) (D := fun t => t/|t|)
    (show LipschitzWith 1 abs from LipschitzWith.of_dist_le_mul (fun x y => by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y)) (measurable_id.div measurable_id.abs) (by norm_num : (0:ℝ) ≤ 1) hb
    (fun j => absApprox (e j)) (fun j => absApproxDeriv (e j)) (fun _ => 1)
    (fun j => absApprox_lipschitz (hepos j)) (fun j => absApprox_hasDerivAt (hepos j))
    (fun j => continuous_absApproxDeriv (hepos j)) (fun j => absApproxDeriv_bound (hepos j))
    (absApproxDeriv_tendsto he hepos) e he (fun j => absApprox_error (hepos j).le) P
  refine ⟨Q,hQ,?_,?_⟩
  · apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
    · filter_upwards [hQ] with x hx
      simp only [hx,Real.norm_eq_abs,abs_abs,le_refl]
    · filter_upwards [hQ] with x hx
      simp only [hx,Real.norm_eq_abs,abs_abs,le_refl]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hG] with w hw
    rw [hw,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)).trans_eq (one_mul _)

lemma nonnegative_minimizer {p A B : ℝ} (hA : 0 ≤ A) (u : q.Sobolev)
    (hu : criticalNorm q.inclusion p u = 1)
    (hmin : ∀ w, energy q.inclusion q.closedGradient A B u * (criticalNorm q.inclusion p w)^2 ≤
      energy q.inclusion q.closedGradient A B w) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ (q.inclusion v) x) ∧
      criticalNorm q.inclusion p v = 1 ∧
      energy q.inclusion q.closedGradient A B v = energy q.inclusion q.closedGradient A B u ∧
      ∀ w, energy q.inclusion q.closedGradient A B v * (criticalNorm q.inclusion p w)^2 ≤
        energy q.inclusion q.closedGradient A B w := by
  obtain ⟨v,hv,hv2,hvg⟩ := q.closed_abs u
  have hvp : criticalNorm q.inclusion p v = 1 := by
    rw [criticalNorm,lpNorm_congr_ae hv _,lpNorm_fun_abs (Lp.aestronglyMeasurable _)]
    exact hu
  have hle : energy q.inclusion q.closedGradient A B v ≤ energy q.inclusion q.closedGradient A B u := by
    dsimp [energy]
    rw [hv2]
    exact add_le_add (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hvg) hA) le_rfl
  have hge := hmin v
  rw [hvp,one_pow,mul_one] at hge
  have heq := le_antisymm hle hge
  refine ⟨v,?_,hvp,heq,?_⟩
  · filter_upwards [hv] with x hx
    rw [hx]
    exact abs_nonneg _
  · simpa only [heq] using hmin

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Sharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma omega_pos {n : ℕ} (hn : 0 < n) : 0 < omega n := by
  rw [omega_gamma hn]
  have h : (0:ℝ) < n := by exact_mod_cast hn
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_Euler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer

lemma abs_power_derivative_bound {p s a b : ℝ} (hp : 2 < p) (hs : |s| ≤ 1) :
    |(p*|a+s*b|^(p-2)*(a+s*b))*b| ≤ p*(|a|+|b|)^p := by
  have hp0 : 0 ≤ p := by linarith
  have hr : 0 ≤ p-2 := by linarith
  let R := |a|+|b|
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb : |b| ≤ R := le_add_of_nonneg_left (abs_nonneg _)
  have ha : |a+s*b| ≤ R := by
    have hh := abs_add_le a (s*b)
    rw [abs_mul] at hh
    have := mul_le_mul_of_nonneg_right hs (abs_nonneg b)
    dsimp [R]
    linarith
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hp0,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hh := mul_le_mul (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) ha hr) hp0)
    ha (abs_nonneg _) (by positivity)) hb (abs_nonneg _) (by positivity)
  apply hh.trans_eq
  change p*R^(p-2)*R*R = p*R^p
  by_cases hR0 : R = 0
  · simp only [hR0,Real.zero_rpow (by linarith : p ≠ 0),mul_zero]
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
    rw [mul_assoc,mul_assoc]
    congr 1
    rw [show R*R = R^(2:ℝ) by rw [Real.rpow_two,pow_two],←Real.rpow_add hRp]
    congr 1
    ring

lemma integral_abs_power_variation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u v : α → ℝ} {p : ℝ} (hp : 2 < p)
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ) :
    Integrable (fun x => (p*|u x|^(p-2)*u x)*v x) μ ∧
      HasDerivAt (fun s : ℝ => ∫ x, |u x+s*v x|^p ∂μ)
        (∫ x, (p*|u x|^(p-2)*u x)*v x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ p-2 := by linarith
  have huM := hu.aestronglyMeasurable
  have hvM := hv.aestronglyMeasurable
  have hm (s : ℝ) : AEStronglyMeasurable (fun x => |u x+s*v x|^p) μ :=
    (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable ((huM.add (hvM.const_mul s)).norm)
  have hi : Integrable (fun x => |u x|^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs] using
      hu.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
  have hb : Integrable (fun x => p*(|u x|+|v x|)^p) μ := by
    have hh := (hu.norm.add hv.norm).integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,Pi.add_apply] at hh
    have hab (x : α) : |(|u x|+|v x|)| = |u x|+|v x| := abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    simp only [hab] at hh
    exact hh.const_mul p
  have hdm : AEStronglyMeasurable (fun x => (p*|u x|^(p-2)*u x)*v x) μ :=
    ((((Real.continuous_rpow_const hr).comp_aestronglyMeasurable huM.norm).const_mul p).mul huM).mul hvM
  have hd (x : α) (s : ℝ) : HasDerivAt (fun t : ℝ => |u x+t*v x|^p)
      ((p*|u x+s*v x|^(p-2)*(u x+s*v x))*v x) s := by
    simpa only [one_mul,Function.comp_def,id_eq] using (hasDerivAt_abs_rpow (u x+s*v x) (by linarith : 1 < p)).comp s
      (((hasDerivAt_id s).mul_const (v x)).const_add (u x))
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => |u x+s*v x|^p)
    (F' := fun s x => (p*|u x+s*v x|^(p-2)*(u x+s*v x))*v x)
    (bound := fun x => p*(|u x|+|v x|)^p)
    (s := Ioo (-1:ℝ) 1) (x₀ := (0:ℝ))
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall hm) (by simpa only [zero_mul,add_zero] using hi)
    (by simpa only [zero_mul,add_zero] using hdm)
    (Eventually.of_forall fun x s hs => by
      rw [Real.norm_eq_abs]
      exact abs_power_derivative_bound hp (abs_le.mpr ⟨hs.1.le,hs.2.le⟩)) hb
    (Eventually.of_forall fun x s _ => hd x s)
  simpa only [zero_mul,add_zero] using hh

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace H] [SeparableSpace H] in
lemma criticalMass_variation (I : H →L[ℝ] Lp ℝ 2 μ) {p : ℝ} (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ) (u v : H) :
    Integrable (fun x => (p*|(I u) x|^(p-2)*(I u) x)*(I v) x) μ ∧
    HasDerivAt (fun s : ℝ => criticalMass I p (u+s • v))
      (∫ x, (p*|(I u) x|^(p-2)*(I u) x)*(I v) x ∂μ) 0 := by
  obtain ⟨hi,hd⟩ := integral_abs_power_variation hp (hm u) (hm v)
  refine ⟨hi,?_⟩
  have he : (fun s : ℝ => criticalMass I p (u+s • v)) =
      (fun s : ℝ => ∫ x, |(I u) x+s*(I v) x|^p ∂μ) := by
    funext s
    dsimp [criticalMass]
    rw [map_add,map_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (I u) (s • I v),Lp.coeFn_smul s (I v)] with x ha hs
    rw [ha,Pi.add_apply,hs]
    rfl
  rw [he]
  exact hd

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace F] in
lemma energy_variation (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (A B : ℝ) (u v : H) :
    HasDerivAt (fun s : ℝ => energy I G A B (u+s • v))
      (2*(A*inner ℝ (G u) (G v)+B*inner ℝ (I u) (I v))) 0 := by
  have hG : HasDerivAt (fun s : ℝ => G u+s • G v) (G v) 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const (G v)).const_add (G u)
  have hI : HasDerivAt (fun s : ℝ => I u+s • I v) (I v) 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const (I v)).const_add (I u)
  have hh := (hG.norm_sq.const_mul A).add (hI.norm_sq.const_mul B)
  simp only [zero_smul,add_zero] at hh
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  · funext s
    simp only [energy,map_add,map_smul,Pi.add_apply]
  · ring

omit [CompleteSpace H] [SeparableSpace H] [CompleteSpace F] in
lemma critical_euler (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (A B : ℝ) {p : ℝ} (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ) (u : H)
    (hu : criticalNorm I p u = 1)
    (hmin : ∀ w, energy I G A B u*(criticalNorm I p w)^2 ≤ energy I G A B w)
    (v : H) :
    A*inner ℝ (G u) (G v)+B*inner ℝ (I u) (I v) =
      energy I G A B u * (∫ x, |(I u) x|^(p-2)*(I u) x*(I v) x ∂μ) := by
  have hp0 : 0 < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hmass : criticalMass I p u = 1 := by rw [criticalMass_eq I hp0,hu,Real.one_rpow]
  obtain ⟨hi,hD⟩ := criticalMass_variation I hp hm u v
  have heint : (∫ x, (p*|(I u) x|^(p-2)*(I u) x)*(I v) x ∂μ) =
      p*(∫ x, |(I u) x|^(p-2)*(I u) x*(I v) x ∂μ) := by
    rw [←integral_const_mul]
    congr 1
    funext x
    ring
  rw [heint] at hD
  have hDr := hD.rpow_const (p := 2/p) (Or.inl (by simpa only [zero_smul,add_zero,hmass] using (one_ne_zero : (1:ℝ) ≠ 0)))
  simp only [zero_smul,add_zero,hmass,Real.one_rpow] at hDr
  let f := fun s : ℝ => energy I G A B (u+s • v)-energy I G A B u*criticalMass I p (u+s • v)^(2/p)
  have hf0 : f 0 = 0 := by simp only [f,zero_smul,add_zero,hmass,Real.one_rpow,mul_one,sub_self]
  have hminf : IsLocalMin f 0 := by
    apply Eventually.of_forall
    intro s
    rw [hf0]
    exact sub_nonneg.mpr (by simpa only [criticalNorm_sq I hp0] using hmin (u+s • v))
  have hd := (energy_variation I G A B u v).sub (hDr.const_mul (energy I G A B u))
  have he := hminf.hasDerivAt_eq_zero hd
  field_simp at he
  nlinarith

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_Nonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma energy_pos_of_criticalNorm_one {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A B p : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (v : H)
    (hv : criticalNorm I p v = 1) : 0 < energy I G A B v := by
  have hI : I v ≠ 0 := by
    intro he
    have hh : criticalNorm I p v = 0 := by
      dsimp [criticalNorm]
      rw [he,lpNorm_congr_ae (Lp.coeFn_zero ℝ 2 μ) _,lpNorm_zero]
    linarith
  exact add_pos_of_nonneg_of_pos (mul_nonneg hA (sq_nonneg _))
    (mul_pos hB (sq_pos_of_pos (norm_pos_iff.mpr hI)))

lemma critical_euler_nonnegative {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (A B : ℝ) {p : ℝ} (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ) (u : H)
    (hu : criticalNorm I p u = 1) (hupos : ∀ᵐ x ∂μ, 0 ≤ I u x)
    (hmin : ∀ v, energy I G A B u*(criticalNorm I p v)^2 ≤ energy I G A B v)
    (ψ : H) : A*inner ℝ (G u) (G ψ)+B*inner ℝ (I u) (I ψ) =
      energy I G A B u*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ) := by
  rw [critical_euler I G A B hp hm u hu hmin ψ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hupos] with x hx
  rw [abs_of_nonneg hx]
  congr 1
  by_cases hx0 : I u x = 0
  · simp only [hx0,Real.zero_rpow (by linarith : p-1 ≠ 0),mul_zero]
  · have hxp : 0 < I u x := lt_of_le_of_ne hx (Ne.symm hx0)
    calc
      (I u x)^(p-2)*(I u x) = (I u x)^(p-2)*(I u x)^(1:ℝ) := by rw [Real.rpow_one]
      _ = (I u x)^((p-2)+1) := (Real.rpow_add hxp _ _).symm
      _ = (I u x)^(p-1) := by congr 1; ring

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma nonnegative_euler_of_minimum {A B p S : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hp : 2 < p)
    (hm : ∀ u, MemLp (q.inclusion u) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT))
    (u : q.Sobolev) (hu : criticalNorm q.inclusion p u = 1)
    (hus : energy q.inclusion q.closedGradient A B u < S)
    (hmin : ∀ w, energy q.inclusion q.closedGradient A B u * (criticalNorm q.inclusion p w)^2 ≤
      energy q.inclusion q.closedGradient A B w) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ (q.inclusion v) x) ∧
      criticalNorm q.inclusion p v = 1 ∧
      0 < energy q.inclusion q.closedGradient A B v ∧
      energy q.inclusion q.closedGradient A B v < S ∧
      (∀ w, energy q.inclusion q.closedGradient A B v * (criticalNorm q.inclusion p w)^2 ≤
        energy q.inclusion q.closedGradient A B w) ∧
      (∀ ψ, A*inner ℝ (q.closedGradient v) (q.closedGradient ψ)+B*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        energy q.inclusion q.closedGradient A B v *
          (∫ x, (q.inclusion v x)^(p-1)*(q.inclusion ψ x) ∂MassMeasure.currentMassMeasure hT)) := by
  obtain ⟨v,hv,hvp,hQ,hminv⟩ := q.nonnegative_minimizer hA u hu hmin
  refine ⟨v,hv,hvp,energy_pos_of_criticalNorm_one q.inclusion q.closedGradient hA hB v hvp,
    by simpa only [hQ] using hus,hminv,?_⟩
  exact fun ψ => critical_euler_nonnegative q.inclusion q.closedGradient A B hp hm v hvp hv hminv ψ

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_nonnegative_euler {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2)) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ (q.inclusion v) x) ∧
      criticalNorm q.inclusion (sobolevP (k+2)) v = 1 ∧
      0 < energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v <
        (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ)) ∧
      (∀ u, energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
        (criticalNorm q.inclusion (sobolevP (k+2)) u)^2 ≤
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) u) ∧
      (∀ ψ : q.Sobolev,
        (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
          (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
          (∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hA : 0 < 4/((k+2:ℝ)-2) := div_pos (by norm_num) hk0
  have hB : 0 < (k+2:ℝ) := by positivity
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hsphere : 0 < sphereArea (k+2) := by
    unfold sphereArea
    exact mul_pos (by positivity) (omega_pos (by omega))
  let S := (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))
  have hS : 0 < S := mul_pos hB (Real.rpow_pos_of_pos hsphere _)
  have hmem : ∀ w : q.Sobolev, MemLp (q.inclusion w)
      (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1) := by
    as_aux_lemma =>
      obtain ⟨C,hC,hb⟩ := extremal_closed_sobolev (k := k) (T := T)
        hk hX hT hz hm q hd hr hfill hext
        (show 0 < S/2 by positivity) (show S/2 < S by linarith)
      exact fun w => (hb w).1
  obtain ⟨u,hu,hus,hmin⟩ := extremal_critical_minimizer (k := k) (T := T)
    hk hX hT hz hm hms q hd hr hfill hext
  as_aux_lemma =>
    exact q.nonnegative_euler_of_minimum (k := k+1) (T := T)
      (A := 4/((k+2:ℝ)-2)) (B := k+2) (p := sobolevP (k+2)) (S := S)
      hA.le hB hp hmem u hu hus hmin

end CAT0Fillings
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma normalized_scalar {p n Λ σ : ℝ} (hp : 2 < p) (hn : 0 < n) (hΛ : 0 < Λ)
    (hσ : 0 < σ) (hsub : Λ < n*σ^((p-2)/p)) :
    let c := (Λ/n)^(1/(p-2))
    0 < c ∧ c*Λ = n*c^(p-1) ∧ c^2*Λ = n*c^p ∧ 0 < c^p ∧ c^p < σ := by
  let c := (Λ/n)^(1/(p-2))
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos hΛ hn) _
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p-2 := by linarith
  have hcp : c^(p-2) = Λ/n := by
    dsimp [c]
    rw [←Real.rpow_mul (div_nonneg hΛ.le hn.le)]
    rw [one_div_mul_cancel hpm.ne',Real.rpow_one]
  have hcpm : c^(p-1) = c^(p-2)*c := by
    calc
      c^(p-1) = c^((p-2)+1) := by congr 1; ring
      _ = c^(p-2)*c^((1:ℝ)) := Real.rpow_add hc _ _
      _ = c^(p-2)*c := by rw [Real.rpow_one]
  have hcpa : c^p = c^(p-2)*c^2 := by
    rw [←Real.rpow_two,←Real.rpow_add hc]
    congr 1
    ring
  have he1 : c*Λ = n*c^(p-1) := by rw [hcpm,hcp]; field_simp
  have he2 : c^2*Λ = n*c^p := by rw [hcpa,hcp]; field_simp
  have hlt : c^(p-2) < σ^((p-2)/p) := by
    rw [hcp]
    exact (div_lt_iff₀ hn).mpr (by simpa only [mul_comm] using hsub)
  have hlt' := Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hlt (div_pos hp0 hpm)
  rw [←Real.rpow_mul hc.le,←Real.rpow_mul hσ.le] at hlt'
  have hp1 : (p-2)*(p/(p-2)) = p := by field_simp
  have hp2 : ((p-2)/p)*(p/(p-2)) = 1 := by field_simp
  rw [hp1,hp2,Real.rpow_one] at hlt'
  exact ⟨hc,he1,he2,Real.rpow_pos_of_pos hc _,hlt'⟩

end CAT0Fillings.AnalyticMinimizer
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_Minimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma sobolevP_ratio {n : ℕ} (hn : 2 < n) : (sobolevP n-2)/sobolevP n = 2/(n:ℝ) := by
  have hn2 : (2:ℝ) < n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn2' : (n:ℝ)-2 ≠ 0 := by linarith
  dsimp [sobolevP]
  field_simp
  ring

end CAT0Fillings
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma normalize_euler_minimum (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A p n σ : ℝ} (hp : 2 < p) (hn : 0 < n) (hσ : 0 < σ) (u : H)
    (hu : criticalNorm I p u = 1) (hupos : ∀ᵐ x ∂μ, 0 ≤ (I u) x)
    (hQ : 0 < energy I G A n u) (hsub : energy I G A n u < n*σ^((p-2)/p))
    (hmin : ∀ f : H, energy I G A n u*(criticalNorm I p f)^2 ≤ energy I G A n f)
    (heuler : ∀ ψ : H, A*inner ℝ (G u) (G ψ)+n*inner ℝ (I u) (I ψ) =
      energy I G A n u*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ)) :
    ∃ v : H,
      (∀ᵐ x ∂μ, 0 ≤ I v x) ∧ 0 < criticalMass I p v ∧ criticalMass I p v < σ ∧
      energy I G A n v = n*criticalMass I p v ∧
      (∀ ψ : H, A*inner ℝ (G v) (G ψ)+n*inner ℝ (I v) (I ψ) =
        n*(∫ x, (I v x)^(p-1)*(I ψ x) ∂μ)) ∧
      (∀ f : H, energy I G A n v*(criticalNorm I p f)^2 ≤
        energy I G A n f*(criticalNorm I p v)^2) := by
  let Λ := energy I G A n u
  let c := (Λ/n)^(1/(p-2))
  obtain ⟨hc,he1,he2,hcp,hcps⟩ := normalized_scalar hp hn hQ hσ hsub
  change 0 < c at hc
  change c*Λ = n*c^(p-1) at he1
  change c^2*Λ = n*c^p at he2
  change 0 < c^p at hcp
  change c^p < σ at hcps
  have hmass : criticalMass I p (c • u) = c^p := by
    rw [criticalMass_eq I (by linarith : 0 < p),criticalNorm_smul,hu,mul_one,abs_of_pos hc]
  refine ⟨c • u,?_,by simpa only [hmass] using hcp,by simpa only [hmass] using hcps,?_,?_,?_⟩
  · rw [map_smul]
    filter_upwards [Lp.coeFn_smul c (I u),hupos] with x hx hp
    rw [hx]
    exact mul_nonneg hc.le hp
  · rw [energy_smul,hmass]
    exact he2
  · intro ψ
    have hi : (∫ x, (I (c • u) x)^(p-1)*(I ψ x) ∂μ) =
        c^(p-1)*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ) := by
      rw [←integral_const_mul,map_smul]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c (I u),hupos] with x hx hp
      rw [hx]
      change (c*(I u x))^(p-1)*(I ψ x) = _
      rw [Real.mul_rpow hc.le hp]
      ring
    rw [hi,map_smul,map_smul,real_inner_smul_left,real_inner_smul_left]
    calc
      A*(c*inner ℝ (G u) (G ψ))+n*(c*inner ℝ (I u) (I ψ)) =
          c*(A*inner ℝ (G u) (G ψ)+n*inner ℝ (I u) (I ψ)) := by ring
      _ = c*Λ*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ) := by rw [heuler]; ring
      _ = n*(c^(p-1)*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ)) := by rw [he1]; ring

  · intro f
    rw [energy_smul,criticalNorm_smul,hu,mul_one,abs_of_pos hc]
    have hh := mul_le_mul_of_nonneg_left (hmin f) (sq_nonneg c)
    nlinarith

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_normalized_minimum {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2)) (q : ChartGeometry hT.1)
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂currentMassMeasure hT.1, 0 ≤ (q.inclusion v) x) ∧
      0 < criticalMass q.inclusion (sobolevP (k+2)) v ∧
      criticalMass q.inclusion (sobolevP (k+2)) v < sphereArea (k+2) ∧
      energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v =
        (k+2:ℝ)*criticalMass q.inclusion (sobolevP (k+2)) v ∧
      (∀ ψ : q.Sobolev,
        (4/((k+2:ℝ)-2))*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
          (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(sobolevP (k+2)-1)*(q.inclusion ψ) x ∂currentMassMeasure hT.1)) ∧
      (∀ f : q.Sobolev,
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) v *
          (criticalNorm q.inclusion (sobolevP (k+2)) f)^2 ≤
        energy q.inclusion q.closedGradient (4/((k+2:ℝ)-2)) (k+2:ℝ) f *
          (criticalNorm q.inclusion (sobolevP (k+2)) v)^2) := by
  have hn : (2:ℝ) < k+2 := by exact_mod_cast (show 2 < k+2 by omega)
  have hk0 : 0 < (k+2:ℝ)-2 := by linarith
  have hp : 2 < sobolevP (k+2) := by
    dsimp [sobolevP]
    push_cast
    exact (lt_div_iff₀ hk0).mpr (by linarith)
  have hB : 0 < (k+2:ℝ) := by positivity
  obtain ⟨u,hupos,hu,hQ,hsub,hmin,heuler⟩ :=
    extremal_nonnegative_euler hk hX hT hz hm hms q hd hr hfill hext
  apply normalize_euler_minimum q.inclusion q.closedGradient hp hB (hm.trans hms) u hu hupos hQ ?_ hmin heuler
  simpa only [sobolevP_ratio (by omega : 2 < k+2),Nat.cast_add,Nat.cast_ofNat] using hsub

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Euler_NormalizedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open ChartGeometry AnalyticMinimizer MassMeasure Rearrangement RadialSobolev

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem normalized_extremal_contradiction_oai {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (hms : mass T < sphereArea (k+2))
    {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hnorm : d*r*(mass T)^(r-1) = 1/(k+2:ℝ))
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B)) : False := by
  obtain ⟨q⟩ := exists_chartGeometry hX hT.1 hT.2.1
  obtain ⟨v,hv,hW,hWs,hE,heuler,hmin⟩ := extremal_normalized_minimum hk hX hT hz hm hms q hd hr hfill hext
  obtain ⟨hmom,hpow⟩ := extremal_euler_powers hk hX hT hz hm q hd hr hfill hext v hv heuler
  let β : ℝ := 1/((k+2:ℝ)-2)
  have hk0 : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  have hb : 0 < β := by dsimp [β]; exact div_pos (by norm_num) (by linarith)
  have hnb : (k+2:ℝ)*β = 1+2*β := by dsimp [β]; simp only [add_sub_cancel_right]; field_simp [hk0.ne']
  have hp : sobolevP (k+2) = 2+4*β := by
    dsimp [sobolevP,β]
    push_cast
    simp only [add_sub_cancel_right]
    field_simp [hk0.ne']
    ring
  have ha : 4/((k+2:ℝ)-2) = 4*β := by dsimp [β]; ring
  have hψ : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+2:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+2:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂currentMassMeasure hT.1) := by
    intro ψ
    simpa only [hp,ha,show 2+4*β-1 = 1+4*β by ring] using heuler ψ
  have hrad (o : X) (g : X → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g)
      (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
      q.radialVariation o g ≤ (k+2:ℝ)*q.sweptMass o g := by
    have h := radial_inequality_of_extremal hX hT hz q hd.le (by linarith : 0 ≤ r) hm hext o hg hg0 hg1
    rw [hnorm] at h
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ (k+2:ℝ) by positivity)
    simpa only [←mul_assoc,mul_one_div_cancel (show (k+2:ℝ) ≠ 0 by positivity),one_mul] using hh
  apply q.euler_chord_contradiction hX (by omega) hz v hb ?_ hv hmom hpow ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hnb
  · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hψ
  · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hrad
  · rwa [hp] at hW
  · rwa [hp] at hWs
  · simpa only [hp,ha,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hE
  · simpa only [hp,ha,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hmin
end CAT0Fillings
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.normalized_extremal_contradiction_oai.{u_1} := @OAI.CAT0Fillings.normalized_extremal_contradiction_oai.{u_1}
