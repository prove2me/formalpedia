-- Prove2me | solution 1 for OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:35:49.631286+00:00
-- url     : https://prove2.me/submissions/70c7d2ec-7bdc-44d0-9d3a-ad6593d48729

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000
import Theorems.Thm_OAI_SharpIntegralFillings_EuclideanStraightening_exists_straightened_pieces

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_DensityPush
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open MeasureTheory

lemma integral_densityPush_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) {ρ : α → ℝ}
    (hρ : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    {b : β → ℝ} (hb : Measurable b) :
    (∫ x, b x ∂densityPush μ φ ρ) = ∫ z, ρ z*b (φ z) ∂μ := by
  rw [densityPush_eq_map μ hφ,integral_map hφ.aemeasurable hb.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hρ0] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

section BorelChartTests
variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
lemma integrable_weighted_comp (μ : Measure Z) {φ : Z → X} (hφ : Measurable φ)
    {w : Z → ℝ} (hw : Integrable w μ) {b : X → ℝ}
    (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M) :
    Integrable (fun z => w z * b (φ z)) μ := by
  obtain ⟨M,hM⟩ := hB
  exact hw.mul_bdd (hb.comp hφ).aestronglyMeasurable
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hM (φ z))

end BorelChartTests
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_DenseTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
universe u

namespace BorelCoefficients

variable {X : Type u} [MetricSpace X] [CompactSpace X]

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma exists_lipschitz_approximation {b : X → ℝ} (hb : Integrable b μ) :
    ∃ f : ℕ → lipAlgebra (X := X),
      Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂μ) atTop (𝓝 0) := by
  obtain ⟨u,hu,hulim⟩ := mem_closure_iff_seq_limit.mp ((lipToL1_dense μ) hb.toL1)
  choose f hf using hu
  have hfun : (fun j => lipToL1 μ (f j)) = u := funext hf
  have hf := hfun ▸ hulim
  refine ⟨f,?_⟩
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero).mp hf
  convert hnorm using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (lipToL1 μ (f j)) hb.toL1,
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ (f j).val,
    hb.coeFn_toL1] with x hx hfx hbx
  change |(f j).val x-b x| = ‖(lipToL1 μ (f j)-hb.toL1) x‖
  rw [hx]
  change _ = ‖(ContinuousMap.toLp 1 μ ℝ (f j).val) x - (hb.toL1) x‖
  rw [hfx,hbx,Real.norm_eq_abs]

end BorelCoefficients
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Control
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open MeasureTheory

section BorelChartTests
variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
theorem signed_chart_control_borel (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {w : Z → ℝ} (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν)
    {b : X → ℝ} (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M) :
    |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν := by
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let η := ν+τ
  have hνη : ν ≤ η := Measure.le_add_right le_rfl
  have hτη : τ ≤ η := Measure.le_add_left le_rfl
  have hbi : Integrable b η := by
    obtain ⟨M,hM⟩ := hB
    exact Integrable.of_bound hb.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  obtain ⟨f,hf⟩ := BorelCoefficients.exists_lipschitz_approximation η hbi
  have hfi (j : ℕ) : Integrable ((f j).val) η :=
    (f j).val.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwb : Integrable (fun z => w z*b (φ z)) μ :=
    integrable_weighted_comp μ hφ hw hb hB
  have hwf (j : ℕ) : Integrable (fun z => w z*(f j).val (φ z)) μ :=
    integrable_weighted_comp μ hφ hw (f j).val.continuous.measurable (f j).property.2
  have hflim : Tendsto (fun j => ∫ z, w z*(f j).val (φ z) ∂μ) atTop
      (𝓝 (∫ z, w z*b (φ z) ∂μ)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub (hwf j) hwb]
    calc |∫ z, w z*(f j).val (φ z)-w z*b (φ z) ∂μ| ≤
          ∫ z, |w z| * |(f j).val (φ z)-b (φ z)| ∂μ := by
            simpa only [←mul_sub,Real.norm_eq_abs,abs_mul] using
              norm_integral_le_integral_norm
                (fun z => w z*(f j).val (φ z)-w z*b (φ z))
      _ = ∫ x, |(f j).val x-b x| ∂τ :=
          (integral_densityPush_measurable μ hφ hw.abs
            (Eventually.of_forall fun _ => abs_nonneg _)
            ((f j).val.continuous.measurable.sub hb).abs).symm
      _ ≤ ∫ x, |(f j).val x-b x| ∂η :=
          integral_mono_measure hτη (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hbi).abs
  have hib : Integrable b ν := hbi.mono_measure hνη
  have hfint : Tendsto (fun j => ∫ x, |(f j).val x| ∂ν) atTop
      (𝓝 (∫ x, |b x| ∂ν)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq,←integral_sub ((hfi j).mono_measure hνη).abs hib.abs]
    calc |∫ x, |(f j).val x|-|b x| ∂ν| ≤ ∫ x, abs (|(f j).val x|-|b x|) ∂ν := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun x => |(f j).val x|-|b x|)
      _ ≤ ∫ x, |(f j).val x-b x| ∂ν :=
          integral_mono_ae (((hfi j).mono_measure hνη).abs.sub hib.abs).abs
            (((hfi j).mono_measure hνη).sub hib).abs
            (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
      _ ≤ ∫ x, |(f j).val x-b x| ∂η :=
          integral_mono_measure hνη (Eventually.of_forall fun _ => abs_nonneg _)
            ((hfi j).sub hbi).abs
  exact le_of_tendsto_of_tendsto hflim.abs hfint
    (Eventually.of_forall fun j => hcontrol _ (f j).property)
end BorelChartTests
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ChangeVariables
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integral_image_eq_integral_abs_det_within {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) :
    ∫ y in f '' s, g y ∂μ =
      ∫ x in s, |(fderivWithin ℝ f s x).det| • g (f x) ∂μ := by
  obtain ⟨t,hts,htm,hteq,htd⟩ := exists_measurable_full_derivative_domain μ hs hf
  calc
    _ = ∫ y in f '' t, g y ∂μ :=
      setIntegral_congr_set (lipschitzOn_image_ae_congr_subset μ hf hts hteq.symm)
    _ = ∫ x in t, |(fderivWithin ℝ f s x).det| • g (f x) ∂μ :=
      integral_image_eq_integral_abs_det_fderiv_smul μ htm htd (hinj.mono hts) g
    _ = _ := setIntegral_congr_set hteq

lemma bilipschitzOn_ae_pullback {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {p : E → Prop} (hp : ∀ᵐ y ∂μ.restrict (f '' s), p y) :
    ∀ᵐ x ∂μ.restrict s, p (f x) := by
  have hinj := antilipschitzOn_injOn ha
  have him := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  have hnull : μ ({y | ¬ p y} ∩ f '' s) = 0 := by
    rwa [ae_iff,Measure.restrict_apply' him] at hp
  rw [ae_iff,Measure.restrict_apply' hs]
  apply measure_mono_null _
    (lipschitzOn_image_null μ ((lipschitzOn_invFunOn ha).mono inter_subset_right) hnull)
  intro x hx
  refine ⟨f x,⟨hx.1,⟨x,hx.2,rfl⟩⟩,?_⟩
  exact hinj.leftInvOn_invFunOn hx.2

lemma ae_fderivWithin_comp_bilipschitzOn {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (ha : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ (L : ℝ) * dist (f x) (f y))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {g : E → V} {J : ℝ≥0} (hg : LipschitzOnWith J g (f '' s)) :
    ∀ᵐ x ∂μ.restrict s, fderivWithin ℝ (g ∘ f) s x =
      (fderivWithin ℝ g (f '' s) (f x)).comp (fderivWithin ℝ f s x) := by
  have hinj := antilipschitzOn_injOn ha
  have him := hs.image_of_continuousOn_injOn hf.continuousOn hinj
  filter_upwards [ae_uniqueDiffWithinAt μ s,hf.ae_differentiableWithinAt hs (μ := μ),
    bilipschitzOn_ae_pullback μ hs hf ha (hg.ae_differentiableWithinAt him (μ := μ))]
    with x hx hfx hgx
  exact fderivWithin_comp x hgx hfx (mapsTo_image f s) hx

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Extensions
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

variable [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] [CompactSpace X] in
lemma integrable_weighted_jacobian {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ)*C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hπ
  exact C.integrable.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_LinearMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma measurableSet_paramExtended_image {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain) :
    MeasurableSet (C.paramExtended '' t) := by
  let := ht.standardBorel
  have hi : Function.Injective (fun z : t => C.paramExtended (z : Euc k)) := by
    intro a b hab
    have hab' : C.param ⟨a,hts a.property⟩ = C.param ⟨b,hts b.property⟩ := by
      simpa only [paramExtended,dite_eq_left (hts a.property),dite_eq_left (hts b.property)] using hab
    obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
    apply Subtype.ext
    exact congrArg (fun z : C.domain => (z : Euc k)) (hU.injective hab')
  have hm := (C.measurable_paramExtended.comp measurable_subtype_coe).measurableEmbedding hi
  have heq : range (fun z : t => C.paramExtended (z : Euc k)) = C.paramExtended '' t := by
    ext x
    simp
  rw [←heq]
  exact hm.measurableSet_range

end IntegerChart
end SharpIntegralFillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_ActionLimits
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
lemma borelAction_sub (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hb : Integrable b μ) (hc : Integrable c μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT (fun x => b x-c x) π =
      borelAction μ hT b π-borelAction μ hT c π := by
  have he : (fun x => b x-c x) = b+(-1 : ℝ) • c := by ext x; simp [sub_eq_add_neg]
  rw [he,borelAction_add μ hT hb (hc.smul (-1)) π hπ,
    borelAction_smul μ hT hc π (-1) hπ]
  ring

lemma borelAction_difference_bound (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b c : X → ℝ} (hb : Integrable b μ) (hc : Integrable c μ)
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    |borelAction μ hT b π-borelAction μ hT c π| ≤
      (∏ i, (K i : ℝ)) * ∫ x, |b x-c x| ∂μ := by
  rw [←borelAction_sub μ hT hb hc π (fun i => ⟨K i,hK i⟩)]
  exact borelAction_bound μ hT hμ (hb.sub hc) π K hK

lemma borelAction_tendsto (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {b : X → ℝ} {f : ℕ → X → ℝ} (hb : Integrable b μ)
    (hf : ∀ j, Integrable (f j) μ)
    (hlim : Tendsto (fun j => ∫ x, |f j x-b x| ∂μ) atTop (𝓝 0))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Tendsto (fun j => borelAction μ hT (f j) π) atTop (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hπ
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => (borelAction_difference_bound μ hT hμ (hf j) hb π K hK))
  simpa only [mul_zero] using hlim.const_mul (∏ i, (K i : ℝ))

end BorelCoefficients
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_CanonicalMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

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

namespace SharpIntegralFillings
namespace MassMeasure
variable {X : Type u} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma weighted_finite (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) : IsFiniteMeasure (weighted μ f) :=
  isFiniteMeasure_withDensity_ofReal
    (hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

omit [CompactSpace X] in
lemma integral_weighted (μ : Measure X) {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) (g : X → ℝ) :
    (∫ x, g x ∂weighted μ f) = ∫ x, f x * g x ∂μ := by
  rw [weighted, integral_withDensity_eq_integral_toReal_smul
    (hf.measurable.ennreal_ofReal) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

omit [CompactSpace X] in
lemma weighted_total (μ : Measure X) {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (weighted μ f).real univ = ∫ x, f x ∂μ := by
  simpa using integral_weighted μ hf hpos (fun _ => 1)

variable {k : ℕ} {T : Functional X k}

lemma controls_splice (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    {f : X → ℝ} (hf : BoundedLip f) (hpos : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ 1) :
    Controls T (weighted μ (fun x => 1 - f x) + weighted ν f) := by
  have hg : BoundedLip (fun x => 1 - f x) := by
    simpa only [neg_mul, one_mul, sub_eq_add_neg] using
      (BoundedLip.const 1).add (hf.const_mul (-1))
  let := weighted_finite μ hg.continuous
  let := weighted_finite ν hf.continuous
  intro b π hb hπ
  have hlin : T b π = T (fun x => b x * (1 - f x)) π + T (fun x => b x * f x) π := by
    have h := hT.linearFirst (fun x => b x * (1-f x)) (fun x => b x * f x) π 1 1
      (hb.mul hg) (hb.mul hf) (fun i => ⟨1, hπ i⟩)
    have heq : (fun x => 1 * (b x * (1-f x)) + 1 * (b x * f x)) = b := by
      funext x; ring
    rwa [heq, one_mul, one_mul] at h
  rw [hlin]
  calc |T (fun x => b x * (1-f x)) π + T (fun x => b x * f x) π| ≤
        |T (fun x => b x * (1-f x)) π| + |T (fun x => b x * f x) π| := abs_add_le _ _
    _ ≤ (∫ x, |b x * (1-f x)| ∂μ) + ∫ x, |b x * f x| ∂ν :=
      add_le_add (hμ _ _ (hb.mul hg) hπ) (hν _ _ (hb.mul hf) hπ)
    _ = ∫ x, |b x| ∂(weighted μ (fun x => 1-f x) + weighted ν f) := by
      rw [integral_add_measure
        (hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
        integral_weighted μ hg.continuous (fun x => sub_nonneg.mpr (hbound x)),
        integral_weighted ν hf.continuous hpos]
      congr 1
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |b x * (1-f x)| = (1-f x) * |b x|
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hbound x)), mul_comm]
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change |b x * f x| = f x * |b x|
          rw [abs_mul, abs_of_nonneg (hpos x), mul_comm]

lemma integral_cutoff_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ)
    {f : X → ℝ} (hf : BoundedLip f) (hpos : ∀ x, 0 ≤ f x) (hbound : ∀ x, f x ≤ 1) :
    (∫ x, f x ∂μ) ≤ ∫ x, f x ∂ν := by
  have hg : Continuous (fun x => 1-f x) := continuous_const.sub hf.continuous
  let := weighted_finite μ hg
  let := weighted_finite ν hf.continuous
  have h := mass_le_measure (T := T)
    (μ := weighted μ (fun x => 1-f x) + weighted ν f) inferInstance
    (controls_splice hT hμ hν hf hpos hbound)
  rw [hm] at h
  have heq : (weighted μ (fun x => 1-f x) + weighted ν f).real univ =
      μ.real univ - (∫ x, f x ∂μ) + ∫ x, f x ∂ν := by
    rw [measureReal_add_apply (by finiteness) (by finiteness),
      weighted_total μ hg (fun x => sub_nonneg.mpr (hbound x)),
      weighted_total ν hf.continuous hpos]
    rw [integral_sub (integrable_const 1)
      (hf.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const, smul_eq_mul, mul_one]
  rw [heq] at h
  linarith

lemma measure_closed_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ) {K : Set X} (hK : IsClosed K) : μ K ≤ ν K := by
  let fs : ℕ → X → ℝ := fun n x =>
    thickenedIndicator (δ := (1 : ℝ)/(n+1)) (by positivity) K x
  have hlimμ : Tendsto (fun n => ∫ x, fs n x ∂μ) atTop (𝓝 (μ.real K)) :=
    tendsto_integral_thickenedIndicator_of_isClosed μ hK (δs := fun n => (1 : ℝ)/(n+1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimν : Tendsto (fun n => ∫ x, fs n x ∂ν) atTop (𝓝 (ν.real K)) :=
    tendsto_integral_thickenedIndicator_of_isClosed ν hK (δs := fun n => (1 : ℝ)/(n+1))
      (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  have hle : ∀ n, (∫ x, fs n x ∂μ) ≤ ∫ x, fs n x ∂ν := by
    intro n
    have hp x : 0 ≤ fs n x := by simp [fs]
    have hb x : fs n x ≤ 1 :=
      thickenedIndicator_le_one _ _ _
    apply integral_cutoff_le hT hμ hν hm _ hp hb
    refine ⟨⟨_, NNReal.isometry_coe.lipschitz.comp
      (lipschitzWith_thickenedIndicator
        (δ := (1 : ℝ)/(n+1)) (by positivity) K)⟩, 1, ?_⟩
    intro x
    rw [abs_of_nonneg (hp x)]
    exact hb x
  exact (ENNReal.toReal_le_toReal (measure_ne_top μ K) (measure_ne_top ν K)).mp
    (le_of_tendsto_of_tendsto hlimμ hlimν (Eventually.of_forall hle))

lemma measure_le (hT : IsMetricCurrent T) {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : Controls T μ) (hν : Controls T ν)
    (hm : mass T = μ.real univ) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => ?_
  exact (measure_closed_le hT hμ hν hm hK.isClosed).trans (measure_mono hKs)

lemma currentMassMeasure_total (hT : IsMetricCurrent T) :
    (currentMassMeasure hT).real univ = mass T :=
  hT.exists_controls_mass_eq.choose_spec.2.2.symm

lemma currentMassMeasure_le (hT : IsMetricCurrent T) {ν : Measure X}
    [IsFiniteMeasure ν] (hν : Controls T ν) : currentMassMeasure hT ≤ ν :=
  measure_le hT (currentMassMeasure_controls hT) hν (currentMassMeasure_total hT).symm

end MassMeasure
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
namespace BorelRestriction
open BorelCoefficients MassMeasure

variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k}

lemma restrictCurrent_apply (hT : IsMetricCurrent T) (E : Set X) {b : X → ℝ}
    {π : Fin k → X → ℝ} (h : Admissible b π) :
    restrictCurrent hT E b π = borelAction (currentMassMeasure hT) hT (E.indicator b) π :=
  ite_eq_left h

lemma restrictCurrent_controls (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) : Controls (restrictCurrent hT E) ((currentMassMeasure hT).restrict E) := by
  intro b π hb hπ
  rw [restrictCurrent_apply hT E ⟨hb, fun i => ⟨1, hπ i⟩⟩]
  have h := borelAction_bound (currentMassMeasure hT) hT (currentMassMeasure_controls hT)
    ((integrable_boundedLip _ hb).indicator hE) π (fun _ => 1) hπ
  simp only [NNReal.coe_one, Finset.prod_const_one, one_mul] at h
  apply h.trans_eq
  rw [← integral_indicator hE]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ E <;> simp [hx]

lemma restrictCurrent_complement_sum (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT E b π + restrictCurrent hT Eᶜ b π = T b π := by
  by_cases h : Admissible b π
  · rw [restrictCurrent_apply hT E h, restrictCurrent_apply hT Eᶜ h,
      ← borelAction_add (currentMassMeasure hT) hT
        ((integrable_boundedLip _ h.1).indicator hE)
        ((integrable_boundedLip _ h.1).indicator hE.compl) π h.2]
    have he : E.indicator b + Eᶜ.indicator b = b := by
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    rw [he]
    exact borelAction_eq _ hT (currentMassMeasure_controls hT) h
  · simp only [restrictCurrent, ite_eq_right h, hT.offDomain b π h, add_zero]

lemma restrictMass_le (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) ≤
      (currentMassMeasure hT).restrict E :=
  currentMassMeasure_le _ (restrictCurrent_controls hT hE)

lemma controls_restriction_sum (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    Controls T (currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) +
      currentMassMeasure (restrictCurrent_isMetricCurrent hT hE.compl)) := by
  intro b π hb hπ
  rw [← restrictCurrent_complement_sum hT hE b π]
  apply (abs_add_le _ _).trans
  rw [integral_add_measure (integrable_boundedLip _ hb).abs (integrable_boundedLip _ hb).abs]
  exact add_le_add (currentMassMeasure_controls (restrictCurrent_isMetricCurrent hT hE) b π hb hπ)
    (currentMassMeasure_controls (restrictCurrent_isMetricCurrent hT hE.compl) b π hb hπ)

lemma restriction_massMeasure (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) =
      (currentMassMeasure hT).restrict E := by
  apply le_antisymm (restrictMass_le hT hE)
  rw [Measure.le_iff]
  intro B hB
  let μ := currentMassMeasure hT
  let ν := currentMassMeasure (restrictCurrent_isMetricCurrent hT hE)
  let ξ := currentMassMeasure (restrictCurrent_isMetricCurrent hT hE.compl)
  have hle : μ ≤ ν + ξ := currentMassMeasure_le hT (controls_restriction_sum hT hE)
  have hξ : ξ (B ∩ E) = 0 := by
    apply le_antisymm _ bot_le
    apply (restrictMass_le hT hE.compl (B ∩ E)).trans
    rw [Measure.restrict_apply (hB.inter hE)]
    have he : B ∩ E ∩ Eᶜ = ∅ := by aesop
    rw [he, measure_empty]
    exact le_refl _
  rw [Measure.restrict_apply hB]
  calc
    μ (B ∩ E) ≤ (ν + ξ) (B ∩ E) := hle _
    _ = ν (B ∩ E) := by rw [Measure.add_apply, hξ, add_zero]
    _ ≤ ν B := measure_mono inter_subset_left

lemma restriction_mass (hT : IsMetricCurrent T) {E : Set X}
    (hE : MeasurableSet E) :
    mass (restrictCurrent hT E) = (currentMassMeasure hT).real E := by
  rw [← currentMassMeasure_total (restrictCurrent_isMetricCurrent hT hE),
    Measure.real, restriction_massMeasure hT hE, Measure.restrict_apply_univ]
  rfl

end BorelRestriction
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_MultiplicityRestriction
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
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

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)
lemma borelAction_eq_integral (hC : IsMetricCurrent C.action)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    {b : X → ℝ} (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hC b π =
      ∫ z, (C.multiplicity z : ℝ)*C.jacobian π z*b (C.paramExtended z)
        ∂volume.restrict C.domain := by
  choose K hK using hπ
  let w : Euc k → ℝ := fun z => (C.multiplicity z : ℝ)*C.jacobian π z
  have hw := C.integrable_weighted_jacobian (fun i => ⟨K i,hK i⟩)
  change Integrable w (volume.restrict C.domain) at hw
  have heq (f : X → ℝ) (hf : BoundedLip f) :
      C.action f π = ∫ z, w z*f (C.paramExtended z) ∂volume.restrict C.domain := by
    rw [action,ite_eq_left ⟨hf,fun i => ⟨K i,hK i⟩⟩]
    apply integral_congr_ae
    filter_upwards [C.scalar_ae_paramExtended f] with z hz
    change C.scalar f z = f (C.paramExtended z) at hz
    rw [hz]
    dsimp [w]
    ring
  have hcontrol (f : X → ℝ) (hf : BoundedLip f) :
      |∫ z, w z*f (C.paramExtended z) ∂volume.restrict C.domain| ≤
        ∫ x, |f x| ∂((∏ i,K i) • μ) := by
    rw [←heq f hf,integral_smul_nnreal_measure]
    simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul] using hC.mass_bound hμ hf K hK
  have hbi : Integrable b μ := by
    obtain ⟨M,hM⟩ := hB
    exact Integrable.of_bound hb.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation μ hbi
  have hfi (j) := integrable_boundedLip μ (f j).property
  have hblim := borelAction_tendsto μ hC hμ hbi hfi hf π (fun i => ⟨K i,hK i⟩)
  have hwbi := integrable_weighted_comp (volume.restrict C.domain)
    C.measurable_paramExtended hw hb hB
  have hwfi (j) := integrable_weighted_comp (volume.restrict C.domain)
    C.measurable_paramExtended hw (f j).val.continuous.measurable (f j).property.2
  have hilim : Tendsto (fun j => ∫ z, w z*(f j).val (C.paramExtended z)
      ∂volume.restrict C.domain) atTop
      (𝓝 (∫ z, w z*b (C.paramExtended z) ∂volume.restrict C.domain)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (by simpa only [mul_zero] using hf.const_mul (∏ i, (K i : ℝ)))
    rw [Real.dist_eq,←integral_sub (hwfi j) hwbi]
    have hsub : (fun z => w z*(f j).val (C.paramExtended z)-w z*b (C.paramExtended z)) =
        (fun z => w z*((f j).val (C.paramExtended z)-b (C.paramExtended z))) := by
      ext z; ring
    rw [hsub]
    have hbnd : ∃ M : ℝ, ∀ x, |(f j).val x-b x| ≤ M := by
      obtain ⟨M,hM⟩ := (f j).property.2
      obtain ⟨N,hN⟩ := hB
      exact ⟨M+N,fun x => (abs_sub _ _).trans (add_le_add (hM x) (hN x))⟩
    have hh := signed_chart_control_borel (volume.restrict C.domain) ((∏ i,K i) • μ)
      C.measurable_paramExtended hw hcontrol
      ((f j).val.continuous.measurable.sub hb) hbnd
    rw [integral_smul_nnreal_measure] at hh
    simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul,Pi.sub_apply] using hh
  have hseq : (fun j => borelAction μ hC (f j).val π) =
      (fun j => ∫ z, w z*(f j).val (C.paramExtended z) ∂volume.restrict C.domain) := by
    ext j
    rw [borelAction_eq μ hC hμ ⟨(f j).property,fun i => ⟨K i,hK i⟩⟩,heq]
    exact (f j).property
  rw [hseq] at hblim
  exact tendsto_nhds_unique hblim hilim

end IntegerChart
end SharpIntegralFillings

namespace SharpIntegralFillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients BorelRestriction MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)

lemma restrictMultiplicity_action (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    (C.restrictMultiplicity E hE).action = restrictCurrent hC E := by
  funext b π
  by_cases hadm : Admissible b π
  · rw [restrictCurrent_apply hC E hadm,
      C.borelAction_eq_integral hC (currentMassMeasure_controls hC)
        (hadm.1.continuous.measurable.indicator hE) ?_ π hadm.2]
    · rw [action,ite_eq_left hadm]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem C.borel] with z hz
      change (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ) * C.scalar b z *
        C.jacobian π z = (C.multiplicity z : ℝ)*C.jacobian π z*E.indicator b (C.paramExtended z)
      have hz' : z ∈ C.domain := hz
      have hs : C.scalar b z = b (C.paramExtended z) := by
        simp only [scalar,paramExtended,dite_eq_left hz']
      rw [hs]
      by_cases he : C.paramExtended z ∈ E <;> simp [he,mul_comm,mul_left_comm]
    · obtain ⟨M,hM⟩ := hadm.1.2
      refine ⟨max M 0,fun x => ?_⟩
      by_cases hx : x ∈ E
      · simpa only [indicator_of_mem hx] using (hM x).trans (le_max_left M 0)
      · simp only [indicator_of_notMem hx,abs_zero,le_max_iff,le_refl,or_true]
  · rw [action,ite_eq_right hadm]
    exact (restrictCurrent_isMetricCurrent hC hE).offDomain b π hadm |>.symm

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_DomainRestriction
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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

namespace SharpIntegralFillings
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma ae_fderivWithin_restrict_domain (μ : Measure E) [μ.IsAddHaarMeasure]
    {s t : Set E} (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : t ⊆ s)
    {f g : E → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hgf : EqOn g f t) :
    ∀ᵐ x ∂μ.restrict t, fderivWithin ℝ g t x = fderivWithin ℝ f s x := by
  obtain ⟨F,hF,hfF⟩ := hf.extend_real
  have hgF : EqOn g F t := fun x hx => (hgf hx).trans (hfF (hts hx))
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ ht hF hgF,
    (ae_fderivWithin_eq_fderiv_extension μ hs hF hfF).filter_mono
      (ae_mono (Measure.restrict_mono hts le_rfl))] with x hx hy
  exact hx.trans hy.symm

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] in
lemma restrictDomain_scalar {t : Set (Euc k)} (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (b : X → ℝ) : EqOn ((C.restrictDomain ht hts).scalar b) (C.scalar b) t := by
  classical
  intro x hx
  change (if hz : x ∈ t then b (C.param ⟨x,hts hz⟩) else 0) = C.scalar b x
  rw [dite_eq_left hx,scalar,dite_eq_left (hts hx)]

omit [MeasurableSpace X] [BorelSpace X] in
lemma restrictDomain_jacobian_ae {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    (C.restrictDomain ht hts).jacobian π =ᵐ[volume.restrict t] C.jacobian π := by
  have hderiv : ∀ᵐ x ∂volume.restrict t, ∀ i,
      fderivWithin ℝ ((C.restrictDomain ht hts).scalar (π i)) t x =
        fderivWithin ℝ (C.scalar (π i)) C.domain x := by
    rw [eventually_all]
    intro i
    obtain ⟨K,hK⟩ := hπ i
    obtain ⟨L,J,hL,_⟩ := C.bilipschitz
    exact ae_fderivWithin_restrict_domain volume C.borel ht hts
      (C.scalar_lipschitzOn hL hK) (C.restrictDomain_scalar ht hts (π i))
  filter_upwards [hderiv] with x hx
  unfold jacobian
  congr 1
  funext i j
  exact congrArg (fun l => l (EuclideanSpace.single j 1)) (hx i)

variable [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma paramExtended_mem_image_iff {t : Set (Euc k)} (hts : t ⊆ C.domain)
    {x : Euc k} (hx : x ∈ C.domain) :
    C.paramExtended x ∈ C.paramExtended '' t ↔ x ∈ t := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨K,J,_,hJ⟩ := C.bilipschitz
    have hxy' : C.param ⟨y,hts hy⟩ = C.param ⟨x,hx⟩ := by
      simpa only [paramExtended,dite_eq_left hx,dite_eq_left (hts hy)] using hxy
    have heq : y = x := congrArg Subtype.val (hJ.injective hxy')
    exact heq ▸ hy
  · exact fun h => ⟨x,h,rfl⟩

lemma restrictDomain_action {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) (hC : IsMetricCurrent C.action) :
    (C.restrictDomain ht hts).action =
      BorelRestriction.restrictCurrent hC (C.paramExtended '' t) := by
  classical
  let E := C.paramExtended '' t
  have hE : MeasurableSet E := C.measurableSet_paramExtended_image ht hts
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hadm : Admissible b π
  · rw [action,action,ite_eq_left hadm,ite_eq_left hadm]
    change (∫ z in t, (C.multiplicity z : ℝ)*(C.restrictDomain ht hts).scalar b z*
      (C.restrictDomain ht hts).jacobian π z) =
      ∫ z in C.domain, (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ)*
        C.scalar b z*C.jacobian π z
    calc
      _ = ∫ z in t, (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z := by
        apply integral_congr_ae
        filter_upwards [C.restrictDomain_jacobian_ae ht hts hadm.2,ae_restrict_mem ht] with z hz hzt
        rw [hz,C.restrictDomain_scalar ht hts b hzt]
      _ = ∫ z in C.domain, t.indicator (fun z =>
          (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z) z := by
        rw [integral_indicator ht,Measure.restrict_restrict ht,inter_eq_left.mpr hts]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem C.borel] with z hz
        have he : z ∈ C.paramExtended ⁻¹' E ↔ z ∈ t := C.paramExtended_mem_image_iff hts hz
        by_cases hzt : z ∈ t
        · simp only [indicator_of_mem hzt,indicator_of_mem (he.mpr hzt)]
        · simp only [indicator_of_notMem hzt,indicator_of_notMem (mt he.mp hzt),Int.cast_zero,zero_mul]
  · simp only [action,ite_eq_right hadm]

end IntegerChart
end SharpIntegralFillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Orientation
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma signed_lipschitzOn_changeVariables {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (hinj : InjOn f s)
    (θ : E → ℤ) (g : E → ℝ) :
    ∫ y in f '' s, ((θ (Function.invFunOn f s y) *
      differentialOrientation (fderivWithin ℝ f s (Function.invFunOn f s y)).det : ℤ) : ℝ) * g y ∂μ =
    ∫ x in s, (θ x : ℝ) * (fderivWithin ℝ f s x).det * g (f x) ∂μ := by
  rw [integral_image_eq_integral_abs_det_within μ hs hf hinj]
  apply setIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [hinj.leftInvOn_invFunOn hx,Int.cast_mul,smul_eq_mul]
  have heq := abs_mul_differentialOrientation (fderivWithin ℝ f s x).det
  calc
    _ = (θ x : ℝ) * (|(fderivWithin ℝ f s x).det| *
      (differentialOrientation (fderivWithin ℝ f s x).det : ℝ)) * g (f x) := by ring
    _ = _ := by rw [heq]

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Reparametrization
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))

lemma reparam_scalar {b : X → ℝ} {x : Euc k} (hx : x ∈ C.domain) :
    (C.reparam f hf ha).scalar b (f x) = C.scalar b x := by
  have hfx : f x ∈ (C.reparam f hf ha).domain := ⟨x,hx,rfl⟩
  rw [(C.reparam f hf ha).scalar_eq hfx,C.scalar_eq hx]
  change b (C.param ⟨Function.invFunOn f C.domain (f x),_⟩) = b (C.param ⟨x,hx⟩)
  congr 2
  apply Subtype.ext
  exact (antilipschitzOn_injOn ha).leftInvOn_invFunOn hx

lemma reparam_image : (C.reparam f hf ha).image = C.image := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨⟨Function.invFunOn f C.domain y,Function.invFunOn_mem y.property⟩,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨⟨f z,⟨z,z.property,rfl⟩⟩,?_⟩
    change C.param ⟨Function.invFunOn f C.domain (f z),_⟩ = C.param z
    congr 1
    apply Subtype.ext
    exact (antilipschitzOn_injOn ha).leftInvOn_invFunOn z.property

end IntegerChart

lemma row_det_comp {k : ℕ} (rows : Fin k → Euc k →L[ℝ] ℝ) (A : Euc k →L[ℝ] Euc k) :
    Matrix.det (fun i j => rows i (A (EuclideanSpace.single j 1))) =
      Matrix.det (fun i j => rows i (EuclideanSpace.single j 1)) * A.det := by
  let B := EuclideanSpace.basisFun (Fin k) ℝ
  have hm : (fun i j => rows i (A (EuclideanSpace.single j 1))) =
      (show Matrix (Fin k) (Fin k) ℝ from fun i j => rows i (EuclideanSpace.single j 1)) * LinearMap.toMatrix B.toBasis B.toBasis A.toLinearMap := by
    ext i j
    rw [Matrix.mul_apply]
    have h := congrArg (rows i) (B.sum_repr (A (EuclideanSpace.single j 1)))
    simp only [_root_.map_sum,map_smul,smul_eq_mul] at h
    simpa only [B,LinearMap.toMatrix_apply,EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr,OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis,ContinuousLinearMap.coe_coe,mul_comm] using h.symm
  rw [hm,Matrix.det_mul,LinearMap.det_toMatrix]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
variable (f : Euc k → Euc k) {K L : ℝ≥0}
  (hf : LipschitzOnWith K f C.domain)
  (ha : ∀ x ∈ C.domain, ∀ y ∈ C.domain,
    dist x y ≤ (L : ℝ) * dist (f x) (f y))

lemma reparam_jacobian_ae {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ J : ℝ≥0, LipschitzWith J (π i)) :
    ∀ᵐ x ∂volume.restrict C.domain, C.jacobian π x =
      (C.reparam f hf ha).jacobian π (f x) * (fderivWithin ℝ f C.domain x).det := by
  have hr : ∀ i, ∀ᵐ x ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (π i)) C.domain x =
        (fderivWithin ℝ ((C.reparam f hf ha).scalar (π i)) (f '' C.domain) (f x)).comp
          (fderivWithin ℝ f C.domain x) := by
    intro i
    obtain ⟨J,hJ⟩ := hπ i
    obtain ⟨U,V,hU,_⟩ := (C.reparam f hf ha).bilipschitz
    have hc := ae_fderivWithin_comp_bilipschitzOn volume C.borel hf ha
      ((C.reparam f hf ha).scalar_lipschitzOn hU hJ)
    filter_upwards [hc,ae_restrict_mem C.borel] with x hx hxs
    have heq : EqOn ((C.reparam f hf ha).scalar (π i) ∘ f) (C.scalar (π i)) C.domain :=
      fun z hz => C.reparam_scalar f hf ha hz
    rwa [fderivWithin_congr' heq hxs] at hx
  filter_upwards [ae_all_iff.mpr hr] with x hx
  unfold jacobian
  simp_rw [hx,ContinuousLinearMap.comp_apply]
  exact row_det_comp _ _

variable [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in

lemma reparam_action : (C.reparam f hf ha).action = C.action := by
  funext b π
  by_cases hbπ : Admissible b π
  · simp only [action,ite_eq_left hbπ]
    change (∫ y in f '' C.domain,
      ((C.multiplicity (Function.invFunOn f C.domain y) * differentialOrientation
        (fderivWithin ℝ f C.domain (Function.invFunOn f C.domain y)).det : ℤ) : ℝ) *
        (C.reparam f hf ha).scalar b y * (C.reparam f hf ha).jacobian π y) = _
    simp_rw [mul_assoc]
    rw [signed_lipschitzOn_changeVariables volume C.borel hf (antilipschitzOn_injOn ha)]
    apply integral_congr_ae
    filter_upwards [C.reparam_jacobian_ae f hf ha hbπ.2,ae_restrict_mem C.borel] with x hx hxs
    rw [C.reparam_scalar f hf ha hxs,hx]
    ring
  · simp only [action,ite_eq_right hbπ]

end IntegerChart
end SharpIntegralFillings
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_DisjointUnions
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

lemma sum_disjoint_indicators {X : Type*} (Z : ℕ → Set X)
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) (b : X → ℝ)
    (s : Finset ℕ) (x : X) :
    ∑ i ∈ s, (Z i).indicator b x = (⋃ i ∈ s, Z i).indicator b x := by
  classical
  by_cases h : ∃ i ∈ s, x ∈ Z i
  · obtain ⟨i,hi,hxi⟩ := h
    rw [indicator_of_mem (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hxi⟩⟩)]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hxi b
    · intro j _ hji
      exact indicator_of_notMem (fun hxj => Set.disjoint_left.mp (hd hji) hxj hxi) b
    · exact fun h => (h hi).elim
  · have hnot : x ∉ ⋃ i ∈ s, Z i := by simpa only [mem_iUnion,exists_prop] using h
    rw [indicator_of_notMem hnot]
    exact Finset.sum_eq_zero fun i hi => indicator_of_notMem (fun hx => h ⟨i,hi,hx⟩) b

namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_finset_sum (hT : IsMetricCurrent T) (f : ℕ → X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (s : Finset ℕ) :
    borelAction μ hT (∑ i ∈ s, f i) π = ∑ i ∈ s, borelAction μ hT (f i) π := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [borelAction_of_integrable μ hT (integrable_zero X ℝ μ) π hπ]
      change l1Action μ hT π hπ 0 = 0
      exact map_zero _
  | @insert i s hi ih =>
      have hs : Integrable (∑ j ∈ s, f j) μ := by
        exact integrable_finsetSum' s (fun j _ => hf j)
      rw [Finset.sum_insert hi,Finset.sum_insert hi,borelAction_add μ hT (hf i) hs π hπ,ih]

lemma borelAction_iUnion (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    HasSum (fun i => borelAction μ hT ((Z i).indicator b) π)
      (borelAction μ hT ((⋃ i, Z i).indicator b) π) := by
  classical
  let g := (⋃ i, Z i).indicator b
  let f (j : ℕ) := (⋃ i ∈ Finset.range j, Z i).indicator b
  have hfi j : Integrable (f j) μ := hb.indicator (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hZ i)
  have hg : Integrable g μ := hb.indicator (MeasurableSet.iUnion hZ)
  have heq j : f j = ∑ i ∈ Finset.range j, (Z i).indicator b := by
    ext x
    simpa only [Finset.sum_apply] using (sum_disjoint_indicators Z hd b (Finset.range j) x).symm
  have hlimx (x : X) : ∀ᶠ j : ℕ in atTop, f j x = g x := by
    by_cases hx : x ∈ ⋃ i, Z i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop (i+1)] with j hj
      change (⋃ i ∈ Finset.range j, Z i).indicator b x = (⋃ i, Z i).indicator b x
      rw [indicator_of_mem hx,indicator_of_mem
        (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hi⟩⟩)]
    · exact Eventually.of_forall fun j => by
        have hxj : x ∉ ⋃ i ∈ Finset.range j, Z i := by
          intro hj
          obtain ⟨i,hi⟩ := mem_iUnion.mp hj
          obtain ⟨_,hxi⟩ := mem_iUnion.mp hi
          exact hx (mem_iUnion.mpr ⟨i,hxi⟩)
        change (⋃ i ∈ Finset.range j, Z i).indicator b x = (⋃ i, Z i).indicator b x
        rw [indicator_of_notMem hx,indicator_of_notMem hxj]
  have hbound j x : |f j x-g x| ≤ |b x|+|b x| := by
    exact (abs_sub _ _).trans (add_le_add (by simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := _) b x)
      (by simpa only [Real.norm_eq_abs] using norm_indicator_le_norm_self (s := _) b x))
  have hlim : Tendsto (fun j => ∫ x, |f j x-g x| ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => |b x|+|b x|)
      (fun j => ((hfi j).sub hg).abs.aestronglyMeasurable) (hb.abs.add hb.abs)
      (fun j => Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply] using hbound j x)
      (Eventually.of_forall fun x =>
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
          ((hlimx x).mono fun j hj => by change 0 = |f j x-g x|; rw [hj,sub_self,abs_zero]))
    simpa only [integral_zero,Pi.sub_apply] using ht
  have ht := borelAction_tendsto μ hT hμ hg hfi hlim π hπ
  have htsum : Summable (fun i => borelAction μ hT ((Z i).indicator b) π) := by
    choose K hK using hπ
    have hsum : Summable (fun i => ∫ x, |(Z i).indicator b x| ∂μ) := by
      have hmeas : (Measure.sum (fun i => μ.restrict (Z i))) = μ.restrict (⋃ i, Z i) :=
        (Measure.restrict_iUnion hd hZ).symm
      have hI : Integrable (fun x => |b x|) (Measure.sum (fun i => μ.restrict (Z i))) := by
        rw [hmeas]
        exact hb.abs.restrict
      convert hI.summable_integral using 1
      all_goals try with_reducible_and_instances rfl
      ext i
      rw [←integral_indicator (hZ i)]
      exact integral_congr_ae (Eventually.of_forall fun x => by
        by_cases hx : x ∈ Z i <;> simp [hx])
    apply (hsum.mul_left (∏ i, (K i : ℝ))).of_norm_bounded
    exact fun i => borelAction_bound μ hT hμ (hb.indicator (hZ i)) π K hK
  apply (hasSum_iff_tendsto_nat_of_summable_norm htsum.norm).mpr
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  ext j
  rw [heq,borelAction_finset_sum μ hT _ (fun i => hb.indicator (hZ i)) π hπ]

end BorelCoefficients
end SharpIntegralFillings
namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology

namespace BorelRestriction
open BorelCoefficients MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k}

lemma restrictCurrent_iUnion (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT (⋃ i, Z i) b π = ∑' i, restrictCurrent hT (Z i) b π := by
  by_cases hab : Admissible b π
  · simp_rw [restrictCurrent_apply hT _ hab]
    exact (borelAction_iUnion (currentMassMeasure hT) hT (currentMassMeasure_controls hT)
      Z hZ hd (integrable_boundedLip _ hab.1) π hab.2).tsum_eq.symm
  · rw [(restrictCurrent_isMetricCurrent hT (MeasurableSet.iUnion hZ)).offDomain b π hab]
    symm
    calc (∑' i, restrictCurrent hT (Z i) b π) = ∑' (_i : ℕ), (0 : ℝ) :=
            tsum_congr fun i => (restrictCurrent_isMetricCurrent hT (hZ i)).offDomain b π hab
      _ = 0 := tsum_zero

lemma summable_restriction_mass (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    Summable (fun i => mass (restrictCurrent hT (Z i))) := by
  simp_rw [restriction_mass hT (hZ _)]
  exact summable_measure_toReal hZ hd

lemma tsum_restriction_mass_le (hT : IsMetricCurrent T)
    (Z : ℕ → Set X) (hZ : ∀ i, MeasurableSet (Z i))
    (hd : Pairwise (fun i j => Disjoint (Z i) (Z j))) :
    (∑' i, mass (restrictCurrent hT (Z i))) ≤ mass T := by
  simp_rw [restriction_mass hT (hZ _),Measure.real]
  rw [← ENNReal.tsum_toReal_eq (fun i => measure_ne_top _ _),←measure_iUnion hd hZ]
  change (currentMassMeasure hT).real (⋃ i, Z i) ≤ mass T
  rw [←currentMassMeasure_total hT]
  exact measureReal_mono (subset_univ _)

end BorelRestriction
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ScalarPieces
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter BorelRestriction EuclideanStraightening
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma paramExtended_disjoint_images (C : IntegerChart X k) {s t : Set (Euc k)}
    (hs : s ⊆ C.domain) (ht : t ⊆ C.domain) (hd : Disjoint s t) :
    Disjoint (C.paramExtended '' s) (C.paramExtended '' t) := by
  rw [Set.disjoint_left] at hd ⊢
  rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hy' : C.paramExtended x ∈ C.paramExtended '' t := ⟨y,hy,heq⟩
  exact hd hx ((C.paramExtended_mem_image_iff ht (hs hx)).mp hy')

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma restrictDomain_image (C : IntegerChart X k) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain) :
    (C.restrictDomain ht hts).image = C.paramExtended '' t := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z,z.property,by simp [paramExtended,restrictDomain,hts z.property]⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨⟨z,hz⟩,?_⟩
    simp [paramExtended,restrictDomain,hts hz]

theorem exists_scalar_straightened_charts_oai (C : IntegerChart X (k+1))
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ D : ℕ → IntegerChart X (k+1),
      Pairwise (fun i j => Disjoint (D i).image (D j).image) ∧
      (∀ i, (D i).image ⊆ C.image) ∧
      (∀ i z (hz : z ∈ (D i).domain),
        u ((D i).param ⟨z,hz⟩) = (Prism.split k z).1) ∧
      Summable (fun i => mass (D i).action) ∧
      (∑' i, mass (D i).action) ≤ mass C.action ∧
      ∀ b π, Admissible b π →
        C.action b (Matrix.vecCons u π) = ∑' i, (D i).action b (Matrix.vecCons u π) := by
  classical
  obtain ⟨L,U,hL,_hU⟩ := C.bilipschitz
  obtain ⟨g,hg,hug⟩ := (C.scalar_lipschitzOn hL hK).extend_real
  obtain ⟨t,dir,J,hts,ht,hd,hbilip,hzero⟩ :=
    exists_straightened_pieces C.borel C.bounded.measure_lt_top.ne hg
  let E i := C.paramExtended '' t i
  have hE i : MeasurableSet (E i) := C.measurableSet_paramExtended_image (ht i) (hts i)
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) :=
    fun i j hij => C.paramExtended_disjoint_images (hts i) (hts j) (hd hij)
  let R i := C.restrictDomain (ht i) (hts i)
  let F i := straightenMap (dir i) g
  have hF i : LipschitzOnWith
      (1+K*L+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊) (F i) (R i).domain :=
    lipschitzOnWith_iff_restrict.mpr (hbilip i).1
  have hA i : ∀ x ∈ (R i).domain, ∀ y ∈ (R i).domain,
      dist x y ≤ (J i:ℝ) * dist (F i x) (F i y) := by
    intro x hx y hy
    exact (hbilip i).2.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
  let D i := (R i).reparam (F i) (hF i) (hA i)
  have hDact i : (D i).action = restrictCurrent C.action_isMetricCurrent (E i) := by
    rw [show (D i).action = (R i).action from (R i).reparam_action _ _ _]
    exact C.restrictDomain_action _ _ C.action_isMetricCurrent
  have hDimage i : (D i).image = E i := by
    rw [show (D i).image = (R i).image from (R i).reparam_image _ _ _]
    exact C.restrictDomain_image _ _
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    rw [hDimage,hDimage]
    exact hEd hij
  · intro i x hx
    rw [hDimage] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    exact ⟨⟨z,hts i hz⟩,by simp [paramExtended,hts i hz]⟩
  · intro i y hy
    let x := Function.invFunOn (F i) (R i).domain y
    have hx : x ∈ (R i).domain := Function.invFunOn_mem hy
    have heq : F i x = y := Function.invFunOn_eq hy
    change u (C.param ⟨x,hts i hx⟩) = (Prism.split k y).1
    have hcx : x ∈ C.domain := hts i hx
    calc
      u (C.param ⟨x,hcx⟩) = C.scalar u x := (C.scalar_eq (f := u) hcx).symm
      _ = g x := hug hcx
      _ = (Prism.split k y).1 := by
        have hc := congrArg (fun w : Euc (k+1) => w 0) heq
        simpa only [F,straightenMap_zero,Prism.split_apply] using hc
  · simp_rw [hDact]
    exact summable_restriction_mass C.action_isMetricCurrent E hE hEd
  · simp_rw [hDact]
    exact tsum_restriction_mass_le C.action_isMetricCurrent E hE hEd
  · intro b π hab
    have hab' : Admissible b (Matrix.vecCons u π) := ⟨hab.1,fun i => by
      cases i using Fin.cases with
      | zero => exact ⟨K,hK⟩
      | succ i => exact hab.2 i⟩
    simp_rw [hDact]
    rw [←restrictCurrent_iUnion C.action_isMetricCurrent E hE hEd,
      ←C.restrictMultiplicity_action C.action_isMetricCurrent (MeasurableSet.iUnion hE)]
    rw [action,action,ite_eq_left hab',ite_eq_left hab']
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel,hzero,
      ae_fderivWithin_eq_fderiv_extension volume C.borel hg hug] with z hz hz0 hder
    change (C.multiplicity z:ℝ)*C.scalar b z*C.jacobian (Matrix.vecCons u π) z =
      ↑((C.paramExtended ⁻¹' ⋃ i, E i).indicator C.multiplicity z)*
        C.scalar b z*C.jacobian (Matrix.vecCons u π) z
    by_cases hzi : z ∈ ⋃ i, t i
    · have him : z ∈ C.paramExtended ⁻¹' ⋃ i, E i := by
        obtain ⟨i,hi⟩ := mem_iUnion.mp hzi
        exact mem_iUnion.mpr ⟨i,⟨z,hi,rfl⟩⟩
      rw [indicator_of_mem him]
    · have hj : C.jacobian (Matrix.vecCons u π) z = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        change (fderivWithin ℝ (C.scalar u) C.domain z) (EuclideanSpace.single j 1) = 0
        rw [hder,hz0 hzi]
        rfl
      rw [hj,mul_zero,mul_zero]

end SharpIntegralFillings.IntegerChart

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts_oai.{u_1} := @OAI.SharpIntegralFillings.IntegerChart.exists_scalar_straightened_charts_oai.{u_1}
