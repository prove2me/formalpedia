-- Prove2me | solution 1 for OAI.SharpIntegralFillings.coefficient_optimal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:34:26.166244+00:00
-- url     : https://prove2.me/submissions/77124543-7cc9-4201-a6d4-a767d8d39712

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000
import Theorems.Thm_OAI_SharpIntegralFillings_IntegerChart_exists_scalar_coarea

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
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Basic
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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

section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

lemma mass_nonneg {k : ℕ} (T : Functional X k) : 0 ≤ mass T := by
  apply Real.sInf_nonneg
  rintro r ⟨μ, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

@[simp] lemma mass_zero (k : ℕ) : mass (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = 0 := by
  apply le_antisymm
  · have h : Controls (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) (0 : Measure X) := by
      intro b π hb hπ
      simp
    simpa using mass_le_measure (μ := (0 : Measure X)) inferInstance h
  · exact mass_nonneg _

lemma integerRectifiable_zero (k : ℕ) :
    IntegerRectifiable (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) := by
  refine ⟨fun _ => emptyChart k, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp
  · intro i
    rw [emptyChart_action]
    exact isMetricCurrent_zero k
  · simp only [emptyChart_action, mass_zero]
    exact summable_zero
  · intro b π
    simp

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]

lemma IsMetricCurrent.mass_bound_uniform [CompactSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i))
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) :
    |T b π| ≤ ((∏ i, (K i : ℝ)) * M) * mass T := by
  obtain ⟨μ, hfin, hcontrol, heq⟩ := hT.exists_controls_mass_eq
  let := hfin
  have hint : Integrable (fun x => |b x|) μ := (hb.toBoundedContinuous.integrable μ).abs
  have hbound : (∫ x, |b x| ∂μ) ≤ μ.real univ * M := by
    simpa using integral_mono hint (integrable_const M) hM
  calc |T b π| ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := hT.mass_bound hcontrol hb K hK
    _ ≤ (∏ i, (K i : ℝ)) * (μ.real univ * M) :=
      mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)
    _ = ((∏ i, (K i : ℝ)) * M) * mass T := by rw [heq]; ring

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_DenseTests
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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
section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]
open scoped BoundedContinuousFunction

variable [BorelSpace X]
lemma summable_actions_of_summable_masses [CompactSpace X]
    {k : ℕ} {Ts : ℕ → Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j))
    (hsum : Summable fun j => mass (Ts j)) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) : Summable fun j => Ts j b π := by
  choose K hK using h.2
  obtain ⟨M, hM⟩ := h.1.2
  apply (hsum.mul_left ((∏ i, (K i : ℝ)) * M)).of_norm_bounded
  intro j
  exact (hTs j).mass_bound_uniform h.1 K hK hM

end Foundations

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

namespace SharpIntegralFillings
open MeasureTheory Set

variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma signed_chart_control_dominates_on_of_measurable
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {s₀ : Set Z}
    (hμ : ∀ᵐ z ∂μ, z ∈ s₀)
    (he : MeasurableEmbedding (fun z : s₀ => φ (z : Z))) {w : Z → ℝ}
    (hwm : Measurable w) (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  classical
  let τ := densityPush μ φ (fun z => |w z|)
  let : IsFiniteMeasure τ := densityPush_finite μ φ hw.abs
  let σ : Z → ℝ := fun z => if w z < 0 then -1 else 1
  have hσm : Measurable σ :=
    Measurable.piecewise (measurableSet_lt hwm measurable_const) measurable_const measurable_const
  have hσabs (z : Z) : |σ z| = 1 := by simp [σ]; split <;> norm_num
  have hσmul (z : Z) : w z * σ z = |w z| := by
    by_cases hz : w z < 0
    · simp [σ,hz,abs_of_neg hz]
    · simp [σ,hz,abs_of_nonneg (le_of_not_gt hz)]
  let σe : X → ℝ := Function.extend (fun z : s₀ => φ (z : Z)) (fun z : s₀ => σ (z : Z)) (fun _ => 0)
  have hσem : Measurable σe := he.measurable_extend (hσm.comp measurable_subtype_coe) measurable_const
  have hσee (z : Z) (hz : z ∈ s₀) : σe (φ z) = σ z :=
    he.injective.extend_apply (fun z : s₀ => σ (z : Z)) (fun _ => 0) ⟨z,hz⟩
  have hσeb (x : X) : |σe x| ≤ 1 := by
    by_cases hx : ∃ z : s₀, φ (z : Z) = x
    · obtain ⟨z,rfl⟩ := hx
      rw [hσee z z.property,hσabs]
    · rw [show σe x = 0 from Function.extend_apply' (fun z : s₀ => σ (z : Z)) (fun _ => 0) x hx]
      norm_num
  apply Measure.le_iff.mpr
  intro s hs
  let b := s.indicator σe
  have hbm : Measurable b := hσem.indicator hs
  have hbb (x : X) : |b x| ≤ s.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ s
    · simpa only [b,indicator_of_mem hx] using hσeb x
    · simp [b,hx]
  have hB : ∃ M : ℝ, ∀ x, |b x| ≤ M := ⟨1,fun x => (hbb x).trans (by
    by_cases hx : x ∈ s <;> simp [hx])⟩
  have hbi : Integrable b ν := Integrable.of_bound hbm.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbb x).trans (by by_cases hx : x ∈ s <;> simp [hx]))
  have heq : (∫ z, w z*b (φ z) ∂μ) = τ.real s := by
    rw [←integral_indicator_one hs]
    rw [show τ = densityPush μ φ (fun z => |w z|) from rfl,
      integral_densityPush_measurable μ hφ hw.abs
        (Eventually.of_forall fun _ => abs_nonneg _)
        (b := s.indicator (1 : X → ℝ)) ((measurable_one : Measurable (1 : X → ℝ)).indicator hs)]
    apply integral_congr_ae
    filter_upwards [hμ] with z hzs
    by_cases hz : φ z ∈ s
    · simpa only [b,indicator_of_mem hz,Pi.one_apply,mul_one,hσee z hzs] using hσmul z
    · simp [b,hz]
  have hc := signed_chart_control_borel μ ν hφ hw hcontrol hbm hB
  rw [heq,abs_of_nonneg (show 0 ≤ τ.real s from ENNReal.toReal_nonneg)] at hc
  have hupper : (∫ x, |b x| ∂ν) ≤ ν.real s := by
    rw [←integral_indicator_one hs]
    exact integral_mono_ae hbi.abs ((integrable_const (1 : ℝ)).indicator hs)
      (Eventually.of_forall hbb)
  exact (ENNReal.toReal_le_toReal (measure_ne_top τ s) (measure_ne_top ν s)).mp
    (hc.trans hupper)

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Differentiability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open MeasureTheory Set

variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
lemma signed_chart_control_dominates_on
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {s₀ : Set Z}
    (hμ : ∀ᵐ z ∂μ, z ∈ s₀)
    (he : MeasurableEmbedding (fun z : s₀ => φ (z : Z))) {w : Z → ℝ}
    (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  let w' := hw.aestronglyMeasurable.mk w
  have heq : w =ᵐ[μ] w' := hw.aestronglyMeasurable.ae_eq_mk
  have hτ : densityPush μ φ (fun z => |w z|) = densityPush μ φ (fun z => |w' z|) := by
    simp only [densityPush_eq_map μ hφ]
    congr 1
    apply withDensity_congr_ae
    exact heq.mono fun z hz => by dsimp only; rw [hz]
  rw [hτ]
  apply signed_chart_control_dominates_on_of_measurable μ ν hφ hμ he
    hw.aestronglyMeasurable.measurable_mk (hw.congr heq)
  intro b hb
  have hi : (∫ z, w' z*b (φ z) ∂μ) = ∫ z, w z*b (φ z) ∂μ :=
    integral_congr_ae (heq.mono fun z hz => by dsimp only; rw [hz])
  rw [hi]
  exact hcontrol b hb
end SharpIntegralFillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Extensions
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)

variable [CompactSpace X]

omit [Nonempty X] in
lemma measurableEmbedding_param : MeasurableEmbedding C.param := by
  let := C.borel.standardBorel
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  exact hL.continuous.measurable.measurableEmbedding hU.injective

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] [CompactSpace X] in
lemma integrable_weighted_jacobian {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ)*C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hπ
  exact C.integrable.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

lemma weighted_jacobian_le_measure
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) ≤ (∏ i, K i) • ν := by
  have he : MeasurableEmbedding (fun z : C.domain => C.paramExtended (z : Euc k)) := by
    convert C.measurableEmbedding_param using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp [paramExtended,z.property]
  apply signed_chart_control_dominates_on (volume.restrict C.domain) ((∏ i,K i) • ν)
    C.measurable_paramExtended (ae_restrict_mem C.borel) he
    (C.integrable_weighted_jacobian (fun i => ⟨K i,hK i⟩))
  intro b hb
  have heq : (∫ z, (C.multiplicity z : ℝ)*C.jacobian π z*b (C.paramExtended z)
      ∂volume.restrict C.domain) = C.action b π := by
    rw [action,ite_eq_left ⟨hb,fun i => ⟨K i,hK i⟩⟩]
    apply integral_congr_ae
    filter_upwards [C.scalar_ae_paramExtended b] with z hz
    dsimp only [Function.comp_apply] at hz
    rw [hz]
    ring
  rw [heq,integral_smul_nnreal_measure]
  simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul] using hC.mass_bound hν hb K hK

end IntegerChart
end SharpIntegralFillings

namespace SharpIntegralFillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_fderivWithin_scalar_eq_linear {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (ℓ : Euc k →L[ℝ] ℝ)
    (heq : ∀ z ∈ t, C.scalar f z = ℓ z) :
    ∀ᵐ z ∂volume.restrict t, fderivWithin ℝ (C.scalar f) C.domain z = ℓ := by
  have hd := (C.ae_differentiableWithinAt_scalar hf).filter_mono
    (ae_mono (Measure.restrict_mono hts le_rfl))
  filter_upwards [hd,ae_uniqueDiffWithinAt volume t,ae_restrict_mem ht] with z hz hu hzt
  rw [←fderivWithin_subset hts hu hz,fderivWithin_congr' heq hzt,ℓ.fderivWithin hu]

lemma exists_inverse_coordinate_tests {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (ℓ : Fin k → Euc k →L[ℝ] ℝ) (K : ℝ≥0)
    (hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y - ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩)) :
    ∃ π : Fin k → X → ℝ, (∀ i, LipschitzWith K (π i)) ∧
      (∀ i, ∀ z ∈ t, C.scalar (π i) z = ℓ i z) ∧
      ∀ᵐ z ∂volume.restrict t,
        C.jacobian π z = (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det := by
  classical
  by_cases hne : t.Nonempty
  · let := hne.to_subtype
    let φ : t → X := fun z => C.param ⟨z,hts z.property⟩
    have hinj : Function.Injective φ := by
      obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : C.domain => (z : Euc k)) (hU.injective hab)
    let q : Fin k → X → ℝ := fun i x => ℓ i ((Function.invFun φ x : t) : Euc k)
    have hq (i : Fin k) : LipschitzOnWith K (q i) (Set.range φ) := by
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      simpa only [q,Function.leftInverse_invFun hinj a,
        Function.leftInverse_invFun hinj b,Real.dist_eq] using
        hrow i a a.property b b.property
    choose π hπ heq using fun i => (hq i).extend_real
    have hagree (i : Fin k) (z : Euc k) (hz : z ∈ t) : C.scalar (π i) z = ℓ i z := by
      rw [C.scalar_eq (hts hz)]
      change π i (φ ⟨z,hz⟩) = _
      rw [←heq i (Set.mem_range_self (⟨z,hz⟩ : t))]
      dsimp only [q]
      rw [Function.leftInverse_invFun hinj]
    refine ⟨π,hπ,hagree,?_⟩
    have hae : ∀ᵐ z ∂volume.restrict t, ∀ i,
        fderivWithin ℝ (C.scalar (π i)) C.domain z = ℓ i :=
      ae_all_iff.mpr fun i => C.ae_fderivWithin_scalar_eq_linear ht hts (hπ i) (ℓ i) (hagree i)
    filter_upwards [hae] with z hz
    simp only [jacobian,hz]
    rfl
  · have ht0 : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst t
    exact ⟨fun _ _ => 0,fun _ => LipschitzWith.const' (0 : ℝ),by simp,by simp⟩

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_LinearMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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

lemma densityPush_congr_ae {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) (φ : Z → X) {ρ σ : Z → ℝ} (h : ρ =ᵐ[μ] σ) :
    densityPush μ φ ρ = densityPush μ φ σ := by
  have hdensity : μ.withDensity (fun point => ENNReal.ofReal (ρ point)) =
      μ.withDensity (fun point => ENNReal.ofReal (σ point)) :=
    withDensity_congr_ae (h.fun_comp ENNReal.ofReal)
  unfold densityPush
  rw [hdensity]

lemma densityPush_restrict_le_restrict_image {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) {φ : Z → X} (hφ : Measurable φ) (ρ : Z → ℝ)
    {t : Set Z} (ht : MeasurableSet t) (him : MeasurableSet (φ '' t)) :
    densityPush (μ.restrict t) φ ρ ≤ (densityPush μ φ ρ).restrict (φ '' t) := by
  simp only [densityPush_eq_map _ hφ]
  rw [←restrict_withDensity ht,Measure.restrict_map hφ him]
  apply Measure.map_mono _ hφ
  apply Measure.restrict_mono _ le_rfl
  intro x hx
  exact ⟨x,hx,rfl⟩

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

lemma linear_piece_mass_le
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (ℓ : Fin k → Euc k →L[ℝ] ℝ) (K : ℝ≥0)
    (hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y - ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩)) :
    densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        |(Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det|)
      ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
  obtain ⟨π,hπ,_,hjac⟩ := C.exists_inverse_coordinate_tests ht hts ℓ K hrow
  have heq : densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        |(Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det|) =
      densityPush (volume.restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) := by
    apply densityPush_congr_ae
    filter_upwards [hjac] with z hz
    rw [hz,abs_mul]
  rw [heq]
  have hrest : (volume.restrict C.domain).restrict t = volume.restrict t := by
    rw [Measure.restrict_restrict ht,inter_eq_left.mpr hts]
  calc
    _ = densityPush ((volume.restrict C.domain).restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) := by rw [hrest]
    _ ≤ (densityPush (volume.restrict C.domain) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|)).restrict
          (C.paramExtended '' t) :=
      densityPush_restrict_le_restrict_image (volume.restrict C.domain)
        C.measurable_paramExtended _ ht (C.measurableSet_paramExtended_image ht hts)
    _ ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
      apply Measure.restrict_mono le_rfl
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        C.weighted_jacobian_le_measure hC hν π (fun _ => K) hπ

end IntegerChart
end SharpIntegralFillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_BoundaryMass
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
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter

lemma vecCons_update_head {α : Type*} {k : ℕ} (b f : α) (π : Fin k → α) :
    Function.update (Matrix.vecCons b π) 0 f = Matrix.vecCons f π := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

namespace SharpIntegralFillings
lemma abs_det_le_prod_row_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le
    (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)))
  rw [Orientation.volumeForm_robust _ b rfl, Module.Basis.det_apply] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  have heq : b.toBasis.toMatrix (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))) = A.transpose := by
    ext i j
    simp [b, Module.Basis.toMatrix_apply]
  rw [heq, Matrix.det_transpose]

lemma row_norm_le_of_dot_bound {n : ℕ} (a : Fin n → ℝ)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_one_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ 1 := by
  apply (abs_det_le_prod_row_norm A).trans
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => row_norm_le_of_dot_bound _ (h i))

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_ProductRule
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
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma admissible_vecCons {k : ℕ} {b f : X → ℝ} {π : Fin k → X → ℝ}
    (hb : BoundedLip b) (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Admissible b (Matrix.vecCons f π) := by
  refine ⟨hb, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hf
  · exact hπ j

end Foundations
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakClosure
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma boundarySucc_boundarySucc {k : ℕ} {T : Functional X (k + 1 + 1)}
    (hT : IsMetricCurrent T) : boundarySucc (boundarySucc T) = fun _ _ => 0 := by
  funext b π
  by_cases h : Admissible b π
  · rw [boundarySucc, ite_eq_left h]
    have hadm : Admissible (fun _ : X => (1 : ℝ)) (Matrix.vecCons b π) :=
      admissible_vecCons (BoundedLip.const 1) h.1.1 h.2
    rw [boundarySucc, ite_eq_left hadm]
    apply hT.eq_zero_of_const_coord (admissible_vecCons (BoundedLip.const 1)
      ⟨0, LipschitzWith.const 1⟩ hadm.2) 0 1
    intro x
    rfl
  · rw [boundarySucc, ite_eq_right h]

end Foundations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_WeakCompactness
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IsMetricCurrent.first_difference_bound {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {b c : X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c)
    (π : Fin k → X → ℝ) (K : ℝ≥0) (hπ : ∀ i, LipschitzWith K (π i))
    (ε : ℝ≥0) (hε : ∀ x, |b x - c x| ≤ ε) :
    |T b π - T c π| ≤ (K : ℝ) ^ k * ε * mass T := by
  have hsub : BoundedLip (fun x => b x - c x) := by
    simpa [sub_eq_add_neg] using hb.add (hc.const_mul (-1))
  have heq : T (fun x => b x - c x) π = T b π - T c π := by
    simpa [sub_eq_add_neg] using hT.linearFirst b c π 1 (-1) hb hc (fun i => ⟨K, hπ i⟩)
  rw [← heq]
  simpa using hT.mass_bound_uniform hsub (fun _ => K) hπ hε

omit [MeasurableSpace X] [BorelSpace X] in
lemma TestClass.boundedLip {d K : ℕ} (p : TestClass (X := X) d K) :
    BoundedLip (p.val.1 : X → ℝ) :=
  ⟨⟨K, p.property.1⟩, K, fun x => (p.val.1.norm_coe_le_norm x).trans p.property.2.1⟩

omit [MeasurableSpace X] [BorelSpace X] in

lemma admissible_mem_testClass {d : ℕ} {b : X → ℝ} {π : Fin d → X → ℝ}
    (h : Admissible b π) :
    ∃ (K : ℕ) (p : TestClass (X := X) d K),
      (p.val.1 : X → ℝ) = b ∧ (fun i => (p.val.2 i : X → ℝ)) = π := by
  obtain ⟨⟨Kb, hb⟩, B, hB⟩ := h.1
  choose Ks hKs using h.2
  let Bn : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let L : ℝ≥0 := max Kb (max Bn (Finset.univ.sup Ks))
  obtain ⟨K, hK⟩ := exists_nat_gt L
  have hbK : Kb ≤ (K : ℝ≥0) := (le_max_left _ _).trans hK.le
  have hBK : Bn ≤ (K : ℝ≥0) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hK.le
  have hπK (i : Fin d) : Ks i ≤ (K : ℝ≥0) :=
    ((Finset.le_sup (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans (le_max_right _ _))).trans hK.le
  let p : C(X, ℝ) × (Fin d → C(X, ℝ)) :=
    (⟨b, hb.continuous⟩, fun i => ⟨π i, (hKs i).continuous⟩)
  refine ⟨K, ⟨p, ⟨hb.weaken hbK, ?_, fun i => (hKs i).weaken (hπK i)⟩⟩, rfl, rfl⟩
  apply (p.1.norm_le (by positivity)).mpr
  intro x
  exact (hB x).trans ((le_max_left B 0).trans hBK)

end Foundations

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_CountableTests
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma IsMetricCurrent.testClass_continuous {d : ℕ} {T : Functional X d}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (d := d) (K := K) T) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have hcoord : Tendsto (fun n => T p.val.1 (fun i => (ps n).val.2 i)) atTop
      (𝓝 (T p.val.1 (fun i => p.val.2 i))) := by
    apply hT.sequentialContinuity _ _ _ p.boundedLip
    · intro i
      exact ⟨K,fun n => (ps n).property.2.2 i⟩
    · intro i x
      have hc : Continuous (fun q : TestClass (X := X) d K => q.val.2 i x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
  have hd : Tendsto (fun n => dist (ps n) p) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hp
  have hbnd (n : ℕ) :
      dist (T p.val.1 (fun i => (ps n).val.2 i))
        (T (ps n).val.1 (fun i => (ps n).val.2 i)) ≤
      ((K:ℝ)^d * mass T) * dist (ps n) p := by
    have hh := IsMetricCurrent.first_difference_bound hT p.boundedLip (ps n).boundedLip
      (fun i => (ps n).val.2 i) K (ps n).property.2.2 (nndist (ps n) p) (fun x => ?_)
    · simpa only [Real.dist_eq,NNReal.coe_natCast,coe_nndist,mul_assoc,mul_comm,mul_left_comm]
        using hh
    · have h := (ContinuousMap.dist_apply_le_dist (f := (ps n).val.1) (g := p.val.1) x).trans
        (le_max_left (dist (ps n).val.1 p.val.1) (dist (ps n).val.2 p.val.2))
      change dist ((ps n).val.1 x) (p.val.1 x) ≤ dist (ps n) p at h
      simpa only [coe_nndist,Real.dist_eq,abs_sub_comm] using h
  apply tendsto_of_tendsto_of_dist hcoord
  exact squeeze_zero (fun n => dist_nonneg) hbnd (by simpa using hd.const_mul ((K:ℝ)^d * mass T))

end SharpIntegralFillings.Foundations

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ChainRule
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.IntegerChart
open Set MeasureTheory Filter

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_fderivWithin_scalar_comp {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (φ ∘ u)) C.domain z =
        dφ (C.scalar u z) • fderivWithin ℝ (C.scalar u) C.domain z := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel,
    C.ae_differentiableWithinAt_scalar hu] with z hz hzs hdu
  have heq : EqOn (C.scalar (φ ∘ u)) (φ ∘ C.scalar u) C.domain := by
    intro y hy
    simp only [Function.comp_apply,C.scalar_eq hy]
  have hh := (hφ (C.scalar u z)).comp_hasFDerivWithinAt z hdu.hasFDerivWithinAt
  exact (hh.congr heq (heq hzs)).fderivWithin hz

lemma ae_jacobian_update_comp (π : Fin k → X → ℝ) (i : Fin k)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (φ ∘ u)) z =
        dφ (C.scalar u z) * C.jacobian (Function.update π i u) z := by
  filter_upwards [C.ae_fderivWithin_scalar_comp hu hφ] with z hz
  rw [C.jacobian_update,C.jacobian_update,hz]
  simpa only [_root_.smul_apply,Pi.smul_def,smul_eq_mul] using Matrix.det_updateRow_smul
    (Matrix.of fun a j => fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1))
    i (dφ (C.scalar u z))
    (fun j => fderivWithin ℝ (C.scalar u) C.domain z (EuclideanSpace.single j 1))

lemma action_update_comp {b u : X → ℝ} (hb : BoundedLip b) (hu : BoundedLip u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    C.action b (Function.update π i (φ ∘ u)) =
      C.action (fun x => b x * dφ (u x)) (Function.update π i u) := by
  obtain ⟨K,hK⟩ := hu.1
  have hup {a : X → ℝ} (ha : BoundedLip a) :
      ∀ j, ∃ K : ℝ≥0, LipschitzWith K ((Function.update π i a) j) := by
    intro j
    by_cases hji : j = i
    · simpa [hji] using ha.1
    · simpa [hji] using hπ j
  rw [action,ite_eq_left ⟨hb,hup hφu⟩,action,ite_eq_left ⟨hb.mul hdu,hup hu⟩]
  apply integral_congr_ae
  filter_upwards [C.ae_jacobian_update_comp π i hK hφ,ae_restrict_mem C.borel] with z hz hzs
  rw [hz,C.scalar_eq hzs,C.scalar_eq hzs,C.scalar_eq hzs]
  ring

end SharpIntegralFillings.IntegerChart

namespace SharpIntegralFillings.Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_update_comp {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b u : X → ℝ} (hb : BoundedLip b) (hu : BoundedLip u)
    {φ dφ : ℝ → ℝ} (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hφu : BoundedLip (φ ∘ u)) (hdu : BoundedLip (dφ ∘ u))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    T b (Function.update π i (φ ∘ u)) =
      T (fun x => b x * dφ (u x)) (Function.update π i u) := by
  obtain ⟨C,_,_,_,heq⟩ := hT
  rw [heq,heq]
  apply tsum_congr
  intro j
  exact (C j).action_update_comp hb hu hφ hφu hdu π hπ i

end SharpIntegralFillings.Foundations

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

lemma borelAction_independent (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν)
    {b : X → ℝ} (hbμ : Integrable b μ) (hbν : Integrable b ν)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hT b π = borelAction ν hT b π := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation (μ+ν) (hbμ.add_measure hbν)
  have hi (j) := integrable_boundedLip (μ+ν) (f j).property
  have hlμ : Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_mono_measure (Measure.le_add_right le_rfl)
        (Eventually.of_forall fun _ => abs_nonneg _) ((hi j).sub (hbμ.add_measure hbν)).abs) hf
  have hlν : Tendsto (fun j => ∫ x, |(f j).val x-b x| ∂ν) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun j => integral_mono_measure (Measure.le_add_left le_rfl)
        (Eventually.of_forall fun _ => abs_nonneg _) ((hi j).sub (hbμ.add_measure hbν)).abs) hf
  have hμlim := borelAction_tendsto μ hT hμ hbμ
    (fun j => integrable_boundedLip μ (f j).property) hlμ π hπ
  have hνlim := borelAction_tendsto ν hT hν hbν
    (fun j => integrable_boundedLip ν (f j).property) hlν π hπ
  simp only [borelAction_eq μ hT hμ ⟨(f _).property,hπ⟩] at hμlim
  simp only [borelAction_eq ν hT hν ⟨(f _).property,hπ⟩] at hνlim
  exact tendsto_nhds_unique hμlim hνlim

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

lemma restrictMultiplicity_isMetricCurrent (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    IsMetricCurrent (C.restrictMultiplicity E hE).action := by
  rw [C.restrictMultiplicity_action hC hE]
  exact restrictCurrent_isMetricCurrent hC hE

lemma restrictMultiplicity_mass_le (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    mass (C.restrictMultiplicity E hE).action ≤ mass C.action := by
  rw [C.restrictMultiplicity_action hC hE,restriction_mass hC hE,
    ←currentMassMeasure_total hC]
  exact measureReal_mono (subset_univ E)

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_ComponentMass
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
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma finite_sum_measure_of_summable_total {X : Type*} [MeasurableSpace X]
    (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hs : Summable (fun i => (μ i).real univ)) : IsFiniteMeasure (Measure.sum μ) := by
  constructor
  have heq : (Measure.sum μ) univ = ENNReal.ofReal (∑' i, (μ i).real univ) := by
    rw [Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.ofReal_tsum_of_nonneg (fun i => measureReal_nonneg) hs]
    congr 1
    funext i
    exact (ENNReal.ofReal_toReal (measure_ne_top (μ i) univ)).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

section SumControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]

lemma controls_sum (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π) : Controls T (Measure.sum μ) := by
  intro b π hb hπ
  have hbi : Integrable (fun x => |b x|) (Measure.sum μ) :=
    (BorelCoefficients.integrable_boundedLip _ hb).abs
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

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_ActionSeries
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
namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  (μ : ℕ → Measure X) [∀ i, IsFiniteMeasure (μ i)] [IsFiniteMeasure (Measure.sum μ)]
omit [IsFiniteMeasure (Measure.sum μ)] in
lemma summable_borelAction (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    {b : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) :
    Summable (fun i => borelAction (μ i) (hS i) b π) := by
  choose K hK using hπ
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hb.abs.summable_integral
  apply (hs.mul_left (∏ j, (K j : ℝ))).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs] using borelAction_bound (μ i) (hS i) (hμ i)
    (hb.mono_measure (Measure.le_sum μ i)) π K hK

omit [IsFiniteMeasure (Measure.sum μ)] in
lemma borelAction_sum_difference_bound (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    {b c : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (hc : Integrable c (Measure.sum μ))
    (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ j, LipschitzWith (K j) (π j)) :
    |(∑' i, borelAction (μ i) (hS i) b π)-(∑' i, borelAction (μ i) (hS i) c π)| ≤
      (∏ j, (K j : ℝ)) * ∫ x, |b x-c x| ∂Measure.sum μ := by
  have hsb := summable_borelAction μ hS hμ hb π (fun j => ⟨K j,hK j⟩)
  have hsc := summable_borelAction μ hS hμ hc π (fun j => ⟨K j,hK j⟩)
  have hbc : Integrable (fun x => b x-c x) (Measure.sum μ) := hb.sub hc
  have hs : Summable (fun i => ∫ x, |b x-c x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbc.abs.summable_integral
  rw [←hsb.tsum_sub hsc,integral_sum_measure hbc.abs,←tsum_mul_left]
  calc
    |∑' i, (borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π)| ≤
      ∑' i, |borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π| := by
        simpa only [Real.norm_eq_abs] using
          (norm_tsum_le_tsum_norm
            (f := fun i => borelAction (μ i) (hS i) b π-borelAction (μ i) (hS i) c π)
            (hsb.sub hsc).norm)
    _ ≤ ∑' i, (∏ j, (K j : ℝ)) * ∫ x, |b x-c x| ∂μ i :=
      (hsb.sub hsc).abs.tsum_le_tsum
        (fun i => borelAction_difference_bound (μ i) (hS i) (hμ i)
          (hb.mono_measure (Measure.le_sum μ i)) (hc.mono_measure (Measure.le_sum μ i)) π K hK)
        (hs.mul_left _)

lemma borelAction_sum (hT : IsMetricCurrent T) (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (heq : ∀ b π, T b π = ∑' i, S i b π)
    {b : X → ℝ} (hb : Integrable b (Measure.sum μ))
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) :
    borelAction (Measure.sum μ) hT b π = ∑' i, borelAction (μ i) (hS i) b π := by
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation (Measure.sum μ) hb
  have hfi (j) := integrable_boundedLip (Measure.sum μ) (f j).property
  have hleft := borelAction_tendsto (Measure.sum μ) hT (controls_sum hμ heq)
    hb hfi hf π hπ
  have hright : Tendsto (fun j => ∑' i, borelAction (μ i) (hS i) (f j).val π) atTop
      (𝓝 (∑' i, borelAction (μ i) (hS i) b π)) := by
    choose K hK using hπ
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun j => borelAction_sum_difference_bound μ hS hμ (hfi j) hb π K hK)
    simpa only [mul_zero] using hf.const_mul (∏ i, (K i : ℝ))
  have hseq : (fun j => borelAction (Measure.sum μ) hT (f j).val π) =
      (fun j => ∑' i, borelAction (μ i) (hS i) (f j).val π) := by
    ext j
    rw [borelAction_eq _ hT (controls_sum hμ heq) ⟨(f j).property,hπ⟩,heq]
    apply tsum_congr
    intro i
    exact (borelAction_eq (μ i) (hS i) (hμ i) ⟨(f j).property,hπ⟩).symm
  rw [hseq] at hleft
  exact tendsto_nhds_unique hleft hright

end BorelCoefficients
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
attribute [local instance] Classical.propDecidable
open BorelCoefficients BorelRestriction MassMeasure

theorem integerRectifiable_restrict
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (hrect : IntegerRectifiable T) {E : Set X} (hE : MeasurableSet E) :
    IntegerRectifiable (restrictCurrent hT E) := by
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hrect
  let D : ℕ → IntegerChart X k := fun i => (C i).restrictMultiplicity E hE
  have hD (i) : IsMetricCurrent (D i).action :=
    (C i).restrictMultiplicity_isMetricCurrent (hC i) hE
  refine ⟨D,hdis,hD,?_,?_⟩
  · apply hsum.of_nonneg_of_le (fun i => mass_nonneg (D i).action)
    exact fun i => (C i).restrictMultiplicity_mass_le (hC i) hE
  · let μ (i) := currentMassMeasure (hC i)
    have hμfin : ∀ i, IsFiniteMeasure (μ i) := fun i => inferInstance
    let := hμfin
    have hμsum : Summable (fun i => (μ i).real univ) := by
      simpa only [μ,currentMassMeasure_total] using hsum
    let := finite_sum_measure_of_summable_total μ hμsum
    have hμ (i) : Controls (C i).action (μ i) := currentMassMeasure_controls (hC i)
    intro b π
    by_cases hab : Admissible b π
    · rw [restrictCurrent_apply hT E hab,
        borelAction_independent (currentMassMeasure hT) hT
          (currentMassMeasure_controls hT) (controls_sum hμ heq)
          ((integrable_boundedLip _ hab.1).indicator hE)
          ((integrable_boundedLip _ hab.1).indicator hE) π hab.2,
        borelAction_sum μ hT hC hμ heq
          ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
      apply tsum_congr
      intro i
      change _ = ((C i).restrictMultiplicity E hE).action b π
      rw [(C i).restrictMultiplicity_action (hC i) hE,restrictCurrent_apply (hC i) E hab]
    · rw [(restrictCurrent_isMetricCurrent hT hE).offDomain b π hab]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π hab)
        _ = 0 := tsum_zero

end SharpIntegralFillings

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
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ContainingCharts
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
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)

variable (hCD : C.domain ⊆ D.domain)
  (hparam : ∀ z : C.domain, C.param z = D.param ⟨z,hCD z.property⟩)

include hCD hparam in
lemma scalar_eqOn_containing (b : X → ℝ) : EqOn (C.scalar b) (D.scalar b) C.domain := by
  intro x hx
  rw [C.scalar_eq hx,D.scalar_eq (hCD hx),hparam ⟨x,hx⟩]

include hCD hparam in
lemma jacobian_eqOn_containing_ae {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    C.jacobian π =ᵐ[volume.restrict C.domain] D.jacobian π := by
  have hrow : ∀ i, ∀ᵐ x ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (π i)) C.domain x =
      fderivWithin ℝ (D.scalar (π i)) D.domain x := by
    intro i
    obtain ⟨K,hK⟩ := hπ i
    obtain ⟨L,U,hL,_⟩ := D.bilipschitz
    exact ae_fderivWithin_restrict_domain volume D.borel C.borel hCD
      (D.scalar_lipschitzOn hL hK) (C.scalar_eqOn_containing D hCD hparam (π i))
  filter_upwards [ae_all_iff.mpr hrow] with x hx
  unfold jacobian
  congr 1
  funext i j
  exact congrArg (fun A => A (EuclideanSpace.single j 1)) (hx i)

include hparam in
lemma extendOn_action : (C.extendOn D hCD).action = C.action := by
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    change (∫ x in D.domain, ((C.domain.indicator C.multiplicity x : ℤ) : ℝ) *
      D.scalar b x * D.jacobian π x) = _
    have heq : (fun x => ((C.domain.indicator C.multiplicity x : ℤ) : ℝ) *
        D.scalar b x * D.jacobian π x) =
        C.domain.indicator (fun x => (C.multiplicity x : ℝ) * D.scalar b x * D.jacobian π x) := by
      funext x
      by_cases hx : x ∈ C.domain <;> simp [hx]
    rw [heq,integral_indicator C.borel,Measure.restrict_restrict C.borel,inter_eq_left.mpr hCD]
    apply integral_congr_ae
    filter_upwards [C.jacobian_eqOn_containing_ae D hCD hparam hab.2,
      ae_restrict_mem C.borel] with x hx hxs
    rw [hx,C.scalar_eqOn_containing D hCD hparam b hxs]
  · simp only [action,ite_eq_right hab]

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ImageRestriction
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
open Set MeasureTheory Filter
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

omit [CompactSpace X] in
lemma restrictImage_image (E : Set X) (hE : MeasurableSet E) :
    (C.restrictImage E hE).image = C.image ∩ E := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨⟨⟨z,z.property.1⟩,rfl⟩,by
      change C.param ⟨z,z.property.1⟩ ∈ E
      simpa only [mem_preimage,paramExtended,dite_eq_left z.property.1] using z.property.2⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    refine ⟨⟨z,⟨z.property,?_⟩⟩,rfl⟩
    simpa only [mem_preimage,paramExtended,dite_eq_left z.property] using hz

lemma restrictImage_action (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) :
    (C.restrictImage E hE).action = BorelRestriction.restrictCurrent hC E := by
  classical
  let t := C.domain ∩ C.paramExtended ⁻¹' E
  have ht : MeasurableSet t := C.borel.inter (C.measurable_paramExtended hE)
  have hts : t ⊆ C.domain := inter_subset_left
  have him : MeasurableSet (C.paramExtended '' t) := C.measurableSet_paramExtended_image ht hts
  change (C.restrictDomain ht hts).action = _
  rw [C.restrictDomain_action ht hts hC,←C.restrictMultiplicity_action hC him,
    ←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    have hi : C.paramExtended z ∈ C.paramExtended '' t ↔ C.paramExtended z ∈ E := by
      rw [C.paramExtended_mem_image_iff hts hz]
      exact and_iff_right hz
    change (↑((C.paramExtended ⁻¹' (C.paramExtended '' t)).indicator C.multiplicity z) : ℝ) *
      C.scalar b z * C.jacobian π z =
      ↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) * C.scalar b z * C.jacobian π z
    by_cases he : C.paramExtended z ∈ E
    · rw [indicator_of_mem (show z ∈ C.paramExtended ⁻¹' (C.paramExtended '' t) from hi.mpr he),
        indicator_of_mem (show z ∈ C.paramExtended ⁻¹' E from he)]
    · rw [indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' (C.paramExtended '' t) from mt hi.mp he),
        indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' E from he)]
  · simp only [action,ite_eq_right hab]

lemma restrictImage_isMetricCurrent (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) : IsMetricCurrent (C.restrictImage E hE).action := by
  rw [C.restrictImage_action E hE hC]
  exact BorelRestriction.restrictCurrent_isMetricCurrent hC hE

lemma restrictImage_mass_le (E : Set X) (hE : MeasurableSet E)
    (hC : IsMetricCurrent C.action) : mass (C.restrictImage E hE).action ≤ mass C.action := by
  rw [C.restrictImage_action E hE hC,BorelRestriction.restriction_mass hC hE,
    ←MassMeasure.currentMassMeasure_total hC]
  exact measureReal_mono (subset_univ E)

lemma restrictCurrent_image_eq (hC : IsMetricCurrent C.action) {E : Set X}
    (hE : MeasurableSet E) (hCE : C.image ⊆ E) :
    BorelRestriction.restrictCurrent hC E = C.action := by
  classical
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    change z ∈ C.domain at hz
    have hi : C.paramExtended z ∈ E := hCE ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩
    change (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ) *
      C.scalar b z * C.jacobian π z = _
    rw [indicator_of_mem (show z ∈ C.paramExtended ⁻¹' E from hi)]
  · simp only [action,ite_eq_right hab]

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Summation
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
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}

lemma summable_actions_all {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i)))
    (b : X → ℝ) (π : Fin k → X → ℝ) : Summable (fun i => T i b π) := by
  by_cases hab : Admissible b π
  · exact summable_actions_of_summable_masses hT hS hab
  · simp only [fun i => (hT i).offDomain b π hab,summable_zero]

theorem isMetricCurrent_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    IsMetricCurrent (fun b π => ∑' i, T i b π) := by
  have hs := summable_actions_all hT hS
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [fun i => (hT i).offDomain b π hab,tsum_zero]
  · intro b c π a d hb hc hπ
    simp only [fun i => (hT i).linearFirst b c π a d hb hc hπ]
    rw [((hs b π).mul_left a).tsum_add ((hs c π).mul_left d)]
    simp only [tsum_mul_left]
  · intro b π j f a c hab hf
    simp only [fun i => (hT i).linearCoord b π j f a c hab hf]
    rw [((hs b π).mul_left a).tsum_add ((hs b (Function.update π j f)).mul_left c)]
    simp only [tsum_mul_left]
  · intro b π πs hb hπs hlim
    choose K hK using hπs
    obtain ⟨M,hM⟩ := hb.2
    apply tendsto_tsum_of_dominated_convergence
      (hS.mul_left ((∏ j, (K j : ℝ)) * M))
      (fun i => (hT i).sequentialContinuity b π πs hb (fun j => ⟨K j,hK j⟩) hlim)
    exact Eventually.of_forall (fun j i => (hT i).mass_bound_uniform hb K (fun l => hK l j) hM)
  · intro b π hab hloc
    simp only [fun i => (hT i).locality b π hab hloc,tsum_zero]
  · choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
    let : ∀ i, IsFiniteMeasure (μ i) := hfin
    have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
    let := finite_sum_measure_of_summable_total μ hm
    exact ⟨Measure.sum μ,inferInstance,controls_sum hμ (fun _ _ => rfl)⟩

lemma mass_tsum_le {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    mass (fun b π => ∑' i, T i b π) ≤ ∑' i, mass (T i) := by
  choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
  let : ∀ i, IsFiniteMeasure (μ i) := hfin
  have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
  let := finite_sum_measure_of_summable_total μ hm
  apply (mass_le_measure (inferInstance : IsFiniteMeasure (Measure.sum μ)) (controls_sum hμ (fun _ _ => rfl))).trans_eq
  rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ, ENNReal.tsum_toReal_eq]
  · exact tsum_congr (fun i => (heq i).symm)
  · intro i
    exact measure_ne_top _ _

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_IntegerSeries
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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma summedMultiplicity_integral_weight {θ : ℕ → X → ℤ}
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) μ)
    (hS : Summable (fun i => ∫ x, |(θ i x : ℝ)| ∂μ))
    {g : X → ℝ} (hg : AEStronglyMeasurable g μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) :
    (∫ x, (summedMultiplicity θ x : ℝ) * g x ∂μ) =
      ∑' i, ∫ x, (θ i x : ℝ) * g x ∂μ := by
  have hI i := (hθ i).mul_bdd hg hM
  have hsum : Summable (fun i => ∫ x, ‖(θ i x : ℝ) * g x‖ ∂μ) := by
    apply (hS.mul_left M).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro i
      rw [←integral_const_mul]
      apply integral_mono_ae (hI i).norm ((hθ i).abs.const_mul M)
      filter_upwards [hM] with x hx
      simpa only [norm_mul,Real.norm_eq_abs,mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg (θ i x : ℝ))
  rw [integral_tsum_of_summable_integral_norm hI hsum]
  apply integral_congr_ae
  filter_upwards with x
  rw [summedMultiplicity_cast,tsum_mul_right]

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_MultiplicityMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
open Set MeasureTheory
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma multiplicity_integral_le_mass (hC : IsMetricCurrent C.action)
    {U : ℝ≥0} (hU : AntilipschitzWith U C.param) :
    (∫ z in C.domain, |(C.multiplicity z : ℝ)|) ≤ (U : ℝ)^k * mass C.action := by
  obtain ⟨ν,hν,hcontrol,hmass⟩ := hC.exists_controls_mass_eq
  let := hν
  have hrow : ∀ (i : Fin k) y (hy : y ∈ C.domain) z (hz : z ∈ C.domain),
      |EuclideanSpace.proj i y - EuclideanSpace.proj i z| ≤
        (U : ℝ) * dist (C.param ⟨y,hy⟩) (C.param ⟨z,hz⟩) := by
    intro i y hy z hz
    calc
      _ = ‖(y-z).ofLp i‖ := by
        change |y.ofLp i-z.ofLp i| = ‖(y-z).ofLp i‖
        simp [Real.norm_eq_abs]
      _ ≤ ‖y-z‖ := PiLp.norm_apply_le (y-z) i
      _ ≤ _ := by simpa only [dist_eq_norm,Subtype.dist_eq] using
        hU.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩
  have hdet : |(Matrix.of fun (i j : Fin k) =>
      EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ))).det| = 1 := by
    have he : (Matrix.of fun (i j : Fin k) =>
        EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ))) = 1 := by
      ext i j
      change (EuclideanSpace.single j (1 : ℝ)).ofLp i = (1 : Matrix (Fin k) (Fin k) ℝ) i j
      simp [PiLp.single_apply,Matrix.one_apply]
    rw [he,Matrix.det_one,abs_one]
  have hle := C.linear_piece_mass_le hC hcontrol C.borel (Subset.refl _)
    (fun i => EuclideanSpace.proj i) U hrow
  simp only [hdet,mul_one] at hle
  have hle' := hle.trans (Measure.restrict_le_self)
  have hI := integral_mono_measure hle' (Eventually.of_forall (fun _ => (zero_le_one : (0:ℝ) ≤ 1)))
    (integrable_const (1 : ℝ) : Integrable (fun _ : X => (1 : ℝ)) ((U^k) • ν))
  rw [integral_densityPush (volume.restrict C.domain) C.measurable_paramExtended
    C.integrable.abs (Eventually.of_forall (fun _ => abs_nonneg _)) continuous_const] at hI
  rw [integral_smul_nnreal_measure] at hI
  simp only [mul_one,integral_const,smul_eq_mul,NNReal.smul_def,NNReal.coe_pow] at hI
  simpa only [hmass,mul_one] using hI

end IntegerChart
end SharpIntegralFillings

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
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Transitions
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
open Set Metric
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C D : IntegerChart X k)

lemma param_inverseParam {x : X} (hx : x ∈ C.image) :
    C.param ⟨C.inverseParam x,C.inverseParam_mem hx⟩ = x := by
  change C.param ⟨if h : x ∈ C.image then (Classical.choose h).val else 0,_⟩ = x
  simpa only [dite_eq_left hx] using (Classical.choose_spec hx)

lemma inverseParam_dist {U : ℝ≥0} (ha : AntilipschitzWith U C.param)
    {x y : X} (hx : x ∈ C.image) (hy : y ∈ C.image) :
    dist (C.inverseParam x) (C.inverseParam y) ≤ (U : ℝ) * dist x y := by
  have h := ha.le_mul_dist ⟨C.inverseParam x,C.inverseParam_mem hx⟩
    ⟨C.inverseParam y,C.inverseParam_mem hy⟩
  simpa only [Subtype.dist_eq,C.param_inverseParam hx,C.param_inverseParam hy] using h

variable (hCD : C.image ⊆ D.image)
include hCD

lemma transition_param {z : Euc k} (hz : z ∈ C.domain) :
    D.param ⟨C.transition D z,C.transition_mem D hCD hz⟩ = C.param ⟨z,hz⟩ := by
  convert D.param_inverseParam (hCD (show C.param ⟨z,hz⟩ ∈ C.image from ⟨⟨z,hz⟩,rfl⟩)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Subtype.ext
  exact C.transition_apply D hz

lemma transition_bilipschitz : ∃ K L : ℝ≥0,
    LipschitzOnWith K (C.transition D) C.domain ∧
    ∀ x ∈ C.domain, ∀ y ∈ C.domain,
      dist x y ≤ (L : ℝ) * dist (C.transition D x) (C.transition D y) := by
  obtain ⟨J,U,hJ,hU⟩ := C.bilipschitz
  obtain ⟨K,V,hK,hV⟩ := D.bilipschitz
  refine ⟨V * J,U * K,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [C.transition_apply D hx,C.transition_apply D hy]
    have h := D.inverseParam_dist hV (hCD ⟨⟨x,hx⟩,rfl⟩) (hCD ⟨⟨y,hy⟩,rfl⟩)
    exact h.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq] using
      mul_le_mul_of_nonneg_left (hJ.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩) V.coe_nonneg)
  · intro x hx y hy
    have h := hU.le_mul_dist ⟨x,hx⟩ ⟨y,hy⟩
    have h' := hK.dist_le_mul ⟨C.transition D x,C.transition_mem D hCD hx⟩
      ⟨C.transition D y,C.transition_mem D hCD hy⟩
    rw [C.transition_param D hCD hx,C.transition_param D hCD hy] at h'
    exact h.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq] using
      mul_le_mul_of_nonneg_left h' U.coe_nonneg)

theorem exists_inCoordinates :
    ∃ E : IntegerChart X k, ∃ hED : E.domain ⊆ D.domain,
      (∀ z : E.domain, E.param z = D.param ⟨z,hED z.property⟩) ∧
      E.action = C.action ∧ E.image = C.image := by
  obtain ⟨K,L,hf,ha⟩ := C.transition_bilipschitz D hCD
  let E := C.reparam (C.transition D) hf ha
  have hED : E.domain ⊆ D.domain := by
    rintro y ⟨x,hx,rfl⟩
    exact C.transition_mem D hCD hx
  refine ⟨E,hED,?_,C.reparam_action _ hf ha,C.reparam_image _ hf ha⟩
  intro z
  let x := Function.invFunOn (C.transition D) C.domain z
  have hx : x ∈ C.domain := Function.invFunOn_mem z.property
  have he : C.transition D x = z := Function.invFunOn_eq z.property
  change C.param ⟨x,hx⟩ = D.param ⟨z,hED z.property⟩
  rw [←C.transition_param D hCD hx]
  congr 1
  exact Subtype.ext he

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_OverlapSum
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
open Set Filter MeasureTheory
open scoped Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma actionWeight_bound {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    ∃ M : ℝ, ∀ᵐ x ∂volume.restrict C.domain, ‖C.scalar b x * C.jacobian π x‖ ≤ M := by
  obtain ⟨M,hM⟩ := hab.1.2
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hab.2
  refine ⟨max M 0 * max B 0,?_⟩
  filter_upwards [hB,ae_restrict_mem C.borel] with x hx hxs
  rw [norm_mul]
  apply mul_le_mul
  · rw [C.scalar_eq hxs,Real.norm_eq_abs]
    exact (hM _).trans (le_max_left _ _)
  · exact hx.trans (le_max_left _ _)
  · exact norm_nonneg _
  · exact le_max_right _ _

lemma sumMultiplicities_action (θ : ℕ → Euc k → ℤ)
    (hθ : ∀ i, Integrable (fun x => (θ i x : ℝ)) (volume.restrict C.domain))
    (hS : Summable (fun i => ∫ x in C.domain, |(θ i x : ℝ)|)) (b : X → ℝ) (π : Fin k → X → ℝ) :
    (C.sumMultiplicities θ hθ hS).action b π =
      ∑' i, (C.withMultiplicity (θ i) (hθ i)).action b π := by
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab]
    change (∫ x in C.domain, (summedMultiplicity θ x : ℝ) * C.scalar b x * C.jacobian π x) =
      ∑' i, ∫ x in C.domain, (θ i x : ℝ) * C.scalar b x * C.jacobian π x
    simp_rw [mul_assoc]
    obtain ⟨M,hM⟩ := C.actionWeight_bound hab
    obtain ⟨K,hK⟩ := hab.1.1
    exact summedMultiplicity_integral_weight hθ hS
      ((C.measurable_scalar hK).aestronglyMeasurable.mul (C.jacobian_aestronglyMeasurable hab.2)) hM
  · simp only [action,ite_eq_right hab,tsum_zero]

end IntegerChart
end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory
open scoped NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}

theorem exists_overlap_sum (D : IntegerChart X k) (C : ℕ → IntegerChart X k)
    (hCD : ∀ i, (C i).image ⊆ D.image) (hC : ∀ i, IsMetricCurrent (C i).action)
    (hS : Summable (fun i => mass (C i).action)) :
    ∃ E : IntegerChart X k, E.image = D.image ∧
      ∀ b π, E.action b π = ∑' i, (C i).action b π := by
  choose F hFD hparam hact him using fun i => (C i).exists_inCoordinates D (hCD i)
  let G (i : ℕ) : IntegerChart X k := (F i).extendOn D (hFD i)
  have hG i : (G i).action = (C i).action :=
    ((F i).extendOn_action D (hFD i) (hparam i)).trans (hact i)
  have hGcurrent i : IsMetricCurrent (G i).action := by rw [hG]; exact hC i
  obtain ⟨L,U,_,hU⟩ := D.bilipschitz
  let θ (i : ℕ) := (G i).multiplicity
  have hθ i : Integrable (fun x => (θ i x : ℝ)) (volume.restrict D.domain) := (G i).integrable
  have hl1 : Summable (fun i => ∫ x in D.domain, |(θ i x : ℝ)|) := by
    apply (hS.mul_left ((U : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact integral_nonneg (fun _ => abs_nonneg _)
    · intro i
      have hbound := (G i).multiplicity_integral_le_mass (hGcurrent i) hU
      change (∫ x in D.domain, |(θ i x : ℝ)|) ≤ (U : ℝ)^k * mass (G i).action at hbound
      simpa only [hG] using hbound
  refine ⟨D.sumMultiplicities θ hθ hl1,rfl,?_⟩
  intro b π
  rw [D.sumMultiplicities_action θ hθ hl1]
  apply tsum_congr
  intro i
  change (G i).action b π = _
  rw [hG]

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Pushforward
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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
namespace CurrentOperations

variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma boundedLip_comp {b : Y → ℝ} (hb : BoundedLip b) {f : X → Y}
    {K : ℝ≥0} (hf : LipschitzWith K f) : BoundedLip (b ∘ f) := by
  obtain ⟨⟨L, hL⟩, M, hM⟩ := hb
  exact ⟨⟨L*K, hL.comp hf⟩, M, fun x => hM (f x)⟩

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma admissible_comp {k : ℕ} {b : Y → ℝ} {π : Fin k → Y → ℝ}
    (h : Admissible b π) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Admissible (b ∘ f) (fun i => π i ∘ f) := by
  refine ⟨boundedLip_comp h.1 hf, fun i => ?_⟩
  obtain ⟨L, hL⟩ := h.2 i
  exact ⟨L*K, hL.comp hf⟩

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_apply {k : ℕ} (f : X → Y) (T : Functional X k)
    {b : Y → ℝ} {π : Fin k → Y → ℝ} (h : Admissible b π) :
    pushCurrent f T b π = T (b ∘ f) (fun i => π i ∘ f) := ite_eq_left h

lemma pushCurrent_controls {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {μ : Measure X} (hμ : Controls T μ) {f : X → Y} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Controls (pushCurrent f T) ((↑(K^k) : ℝ≥0∞) • μ.map f) := by
  intro b π hb hπ
  rw [pushCurrent_apply f T ⟨hb, fun i => ⟨1, hπ i⟩⟩,
    integral_smul_measure, integral_map hf.continuous.aemeasurable
      hb.continuous.abs.aestronglyMeasurable]
  have h := hT.mass_bound hμ (boundedLip_comp hb hf) (fun _ => K)
    (fun i => by simpa only [one_mul] using (hπ i).comp hf)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.coe_toReal, NNReal.coe_pow, smul_eq_mul, Function.comp_apply] using h

lemma pushCurrent_isMetricCurrent {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsMetricCurrent (pushCurrent f T) where
  offDomain := by intro b π h; exact ite_eq_right h
  linearFirst := by
    intro b c π a d hb hc hπ
    rw [pushCurrent_apply f T ⟨(hb.const_mul a).add (hc.const_mul d), hπ⟩,
      pushCurrent_apply f T ⟨hb, hπ⟩, pushCurrent_apply f T ⟨hc, hπ⟩]
    exact hT.linearFirst (b ∘ f) (c ∘ f) (fun i => π i ∘ f) a d
      (boundedLip_comp hb hf) (boundedLip_comp hc hf) (admissible_comp ⟨hb, hπ⟩ hf).2
  linearCoord := by
    intro b π i g a c h hg
    have hπg : ∀ j, ∃ L : ℝ≥0, LipschitzWith L ((Function.update π i g) j) := by
      intro j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hg
      · simpa only [Function.update_of_ne hj] using h.2 j
    have hl : ∃ L : ℝ≥0, LipschitzWith L (fun y => a * π i y + c * g y) := by
      obtain ⟨L, hL⟩ := h.2 i
      obtain ⟨M, hM⟩ := hg
      exact ⟨_, (lipschitz_mul_real hL a).add (lipschitz_mul_real hM c)⟩
    have hπac : ∀ j, ∃ L : ℝ≥0,
        LipschitzWith L ((Function.update π i (fun y => a * π i y + c * g y)) j) := by
      intro j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hl
      · simpa only [Function.update_of_ne hj] using h.2 j
    rw [pushCurrent_apply f T ⟨h.1, hπac⟩, pushCurrent_apply f T h,
      pushCurrent_apply f T ⟨h.1, hπg⟩]
    have h₁ : (fun j => (Function.update π i (fun y => a * π i y + c * g y)) j ∘ f) =
        Function.update (fun j => π j ∘ f) i (fun x => a * π i (f x) + c * g (f x)) := by
      funext j x
      by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
    have h₂ : (fun j => (Function.update π i g) j ∘ f) =
        Function.update (fun j => π j ∘ f) i (g ∘ f) := by
      funext j x
      by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
    rw [h₁, h₂]
    obtain ⟨L, hL⟩ := hg
    exact hT.linearCoord _ _ i _ a c (admissible_comp h hf) ⟨L*K, hL.comp hf⟩
  sequentialContinuity := by
    intro b π πs hb hLip hpt
    choose L hL using hLip
    have hπ (i) : LipschitzWith (L i) (π i) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hL i j).dist_le_mul x y)
    simp only [pushCurrent_apply f T ⟨hb, fun i => ⟨L i, hL i _⟩⟩,
      pushCurrent_apply f T ⟨hb, fun i => ⟨L i, hπ i⟩⟩]
    exact hT.sequentialContinuity _ _ _ (boundedLip_comp hb hf)
      (fun i => ⟨L i*K, fun j => (hL i j).comp hf⟩) (fun i x => hpt i (f x))
  locality := by
    intro b π h hloc
    rw [pushCurrent_apply f T h]
    obtain ⟨i, U, c, hU, hbU, hc⟩ := hloc
    apply hT.locality _ _ (admissible_comp h hf)
    refine ⟨i, f ⁻¹' U, c, hU.preimage hf.continuous, ?_, ?_⟩
    · intro x hx; exact hbU hx
    · intro x hx; exact hc (f x) hx
  finiteMass := by
    obtain ⟨μ, hμ, hctrl⟩ := hT.finiteMass
    let := hμ
    refine ⟨(↑(K^k) : ℝ≥0∞) • μ.map f, ⟨?_⟩, pushCurrent_controls hT hctrl hf⟩
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (μ.map f) univ)

end CurrentOperations
end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Postcompose
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory
open CurrentOperations

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {k : ℕ}
  (C : IntegerChart X k) {f : X → Y} {K J : ℝ≥0}

lemma postcompose_scalar (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) (b : Y → ℝ) :
    (C.postcompose hf hJ).scalar b = C.scalar (b ∘ f) := by
  classical
  funext x
  change (if h : x ∈ C.domain then b (f (C.param ⟨x,h⟩)) else 0) = _
  rfl

lemma postcompose_jacobian (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) (π : Fin k → Y → ℝ) :
    (C.postcompose hf hJ).jacobian π = C.jacobian (fun i => π i ∘ f) := by
  rfl

lemma postcompose_action (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) :
    (C.postcompose hf hJ).action = pushCurrent f C.action := by
  classical
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply f C.action h,action,ite_eq_left h,
      action,ite_eq_left (admissible_comp h hf)]
    change (∫ x in C.domain, (C.multiplicity x : ℝ)*
      (C.postcompose hf hJ).scalar b x*(C.postcompose hf hJ).jacobian π x) = _
    rw [C.postcompose_scalar hf hJ,C.postcompose_jacobian hf hJ]
  · simp only [action,pushCurrent,ite_eq_right h]

lemma postcompose_image (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) :
    (C.postcompose hf hJ).image = f '' C.image := by
  exact range_comp f C.param

end IntegerChart

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_RectifiableMass
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
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma measurableSet_image : MeasurableSet C.image := by
  have heq : C.image = C.paramExtended '' C.domain := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z,z.property,by simp only [paramExtended,dite_eq_left z.property]⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩
  rw [heq]
  exact C.measurableSet_paramExtended_image C.borel (Subset.rfl)

end IntegerChart

end SharpIntegralFillings

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
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_ChartSums
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
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma restrictCurrent_sum {T : Functional X k} {S : ℕ → Functional X k}
    (hT : IsMetricCurrent T) (hS : ∀ i, IsMetricCurrent (S i))
    (hsum : Summable (fun i => mass (S i)))
    (heq : ∀ b π, T b π = ∑' i, S i b π) {E : Set X} (hE : MeasurableSet E)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    restrictCurrent hT E b π = ∑' i, restrictCurrent (hS i) E b π := by
  let μ (i) := currentMassMeasure (hS i)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := fun i => inferInstance
  let := hμfin
  have hμsum : Summable (fun i => (μ i).real univ) := by
    simpa only [μ,currentMassMeasure_total] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  have hμ (i) : Controls (S i) (μ i) := currentMassMeasure_controls (hS i)
  by_cases hab : Admissible b π
  · rw [restrictCurrent_apply hT E hab,
      borelAction_independent (currentMassMeasure hT) hT
        (currentMassMeasure_controls hT) (controls_sum hμ heq)
        ((integrable_boundedLip _ hab.1).indicator hE)
        ((integrable_boundedLip _ hab.1).indicator hE) π hab.2,
      borelAction_sum μ hT hS hμ heq
        ((integrable_boundedLip _ hab.1).indicator hE) π hab.2]
    exact tsum_congr fun i => (restrictCurrent_apply (hS i) E hab).symm
  · rw [(restrictCurrent_isMetricCurrent hT hE).offDomain b π hab]
    symm
    calc (∑' i, restrictCurrent (hS i) E b π) = ∑' (_i : ℕ), (0 : ℝ) :=
            tsum_congr fun i => (restrictCurrent_isMetricCurrent (hS i) hE).offDomain b π hab
      _ = 0 := tsum_zero

theorem integerRectifiable_chartSum [Nonempty X] (C : ℕ → IntegerChart X k)
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action)) :
    IntegerRectifiable (fun b π => ∑' i, (C i).action b π) := by
  let T : Functional X k := fun b π => ∑' i, (C i).action b π
  have hT : IsMetricCurrent T := isMetricCurrent_tsum hC hsum
  let Z : ℕ → Set X := disjointed (fun i => (C i).image)
  have hZ i : MeasurableSet (Z i) := MeasurableSet.disjointed (fun i => (C i).measurableSet_image) i
  have hd : Pairwise (fun i j => Disjoint (Z i) (Z j)) := disjoint_disjointed _
  have hZi i : Z i ⊆ (C i).image := disjointed_subset _ i
  have hZunion : (⋃ i, Z i) = ⋃ i, (C i).image := iUnion_disjointed
  let D i := (C i).restrictImage (Z i) (hZ i)
  have hDim i : (D i).image = Z i := by
    rw [IntegerChart.restrictImage_image,inter_eq_right.mpr (hZi i)]
  let F i j := (C j).restrictImage (Z i) (hZ i)
  have hF i j : IsMetricCurrent (F i j).action := (C j).restrictImage_isMetricCurrent _ _ (hC j)
  have hFS i : Summable (fun j => mass (F i j).action) :=
    hsum.of_nonneg_of_le (fun j => mass_nonneg _) (fun j => (C j).restrictImage_mass_le _ _ (hC j))
  have hFD i j : (F i j).image ⊆ (D i).image := by
    rw [hDim,IntegerChart.restrictImage_image]
    exact inter_subset_right
  choose E hEim hEact using fun i => IntegerChart.exists_overlap_sum (D i) (F i) (hFD i) (hF i) (hFS i)
  have hEeq i : (E i).action = restrictCurrent hT (Z i) := by
    funext b π
    rw [hEact,restrictCurrent_sum hT hC hsum (fun _ _ => rfl) (hZ i)]
    apply tsum_congr
    intro j
    exact congrFun (congrFun ((C j).restrictImage_action _ _ (hC j)) b) π
  have hEcurrent i : IsMetricCurrent (E i).action := by
    rw [hEeq]
    exact restrictCurrent_isMetricCurrent hT (hZ i)
  refine ⟨E,?_,hEcurrent,?_,?_⟩
  · intro i j hij
    simpa only [hEim,hDim] using hd hij
  · simp_rw [hEeq]
    exact summable_restriction_mass hT Z hZ hd
  · intro b π
    simp_rw [hEeq]
    rw [←restrictCurrent_iUnion hT Z hZ hd,hZunion,
      restrictCurrent_sum hT hC hsum (fun _ _ => rfl)
        (MeasurableSet.iUnion fun i => (C i).measurableSet_image)]
    apply tsum_congr
    intro i
    rw [(C i).restrictCurrent_image_eq (hC i)
      (MeasurableSet.iUnion fun i => (C i).measurableSet_image) (subset_iUnion (fun i => (C i).image) i)]

end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory Filter BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}

lemma IntegerChart.restrictCurrent_disjoint_eq_zero (C : IntegerChart X k)
    (hC : IsMetricCurrent C.action) {E : Set X} (hE : MeasurableSet E)
    (hd : Disjoint C.image E) : restrictCurrent hC E = 0 := by
  classical
  rw [←C.restrictMultiplicity_action hC hE]
  funext b π
  by_cases hab : Admissible b π
  · simp only [IntegerChart.action,ite_eq_left hab,Pi.zero_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem C.borel] with z hz
    change z ∈ C.domain at hz
    have hi : C.paramExtended z ∉ E := by
      apply Set.disjoint_left.mp hd
      exact ⟨⟨z,hz⟩,by simp only [IntegerChart.paramExtended,dite_eq_left hz]⟩
    change ↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) * C.scalar b z * C.jacobian π z = 0
    rw [indicator_of_notMem (show z ∉ C.paramExtended ⁻¹' E from hi),Int.cast_zero,zero_mul,zero_mul]
  · simp only [IntegerChart.action,ite_eq_right hab,Pi.zero_apply]

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_PushBoundary
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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
namespace CurrentOperations
variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in

lemma pushCurrent_boundarySucc {k : ℕ} (T : Functional X (k+1))
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    boundarySucc (pushCurrent f T) = pushCurrent f (boundarySucc T) := by
  funext b π
  by_cases h : Admissible b π
  · have hcons : Admissible (fun _ : Y => (1 : ℝ)) (Matrix.vecCons b π) := by
      refine ⟨BoundedLip.const 1, ?_⟩
      intro i
      refine Fin.cases h.1.1 (fun j => h.2 j) i
    rw [boundarySucc, ite_eq_left h, pushCurrent_apply f T hcons,
      pushCurrent_apply f (boundarySucc T) h, boundarySucc,
      ite_eq_left (admissible_comp h hf)]
    congr 1
    funext i x
    exact Fin.cases rfl (fun _ => rfl) i
  · simp only [boundarySucc, pushCurrent, ite_eq_right h]

lemma mass_pushCurrent_le [CompactSpace X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    mass (pushCurrent f T) ≤ (K : ℝ)^k * mass T := by
  obtain ⟨μ, hμ, hc, hm⟩ := hT.exists_controls_mass_eq
  let := hμ
  have hfin : IsFiniteMeasure ((↑(K^k) : ℝ≥0∞) • μ.map f) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (μ.map f) univ)
  calc
    mass (pushCurrent f T) ≤ (((↑(K^k) : ℝ≥0∞) • μ.map f)).real univ :=
      mass_le_measure hfin (pushCurrent_controls hT hc hf)
    _ = (K : ℝ)^k * mass T := by
      rw [hm]
      simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, NNReal.coe_pow, Measure.map_apply hf.continuous.measurable
          MeasurableSet.univ, preimage_univ]

end CurrentOperations
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_IntegralPush
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory
open CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X]

lemma integerRectifiable_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hdis,hC,hm,heq⟩ := hT
  choose L U hL hU using fun i => (C i).bilipschitz
  let D : ℕ → IntegerChart Y k := fun i => (C i).postcompose hf (hfJ.comp (hU i))
  have hDaction (i : ℕ) : (D i).action = pushCurrent f (C i).action :=
    (C i).postcompose_action hf (hfJ.comp (hU i))
  have hD (i : ℕ) : IsMetricCurrent (D i).action := by
    rw [hDaction]
    exact pushCurrent_isMetricCurrent (hC i) hf
  refine ⟨D,?_,hD,?_,?_⟩
  · intro i j hij
    change Disjoint ((C i).postcompose hf _).image ((C j).postcompose hf _).image
    rw [(C i).postcompose_image,(C j).postcompose_image]
    exact (Set.disjoint_image_iff hfJ.injective).mpr (hdis hij)
  · apply (hm.mul_left ((K : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact mass_nonneg (D i).action
    · intro i
      rw [hDaction]
      exact mass_pushCurrent_le (hC i) hf
  · intro b π
    by_cases h : Admissible b π
    · rw [pushCurrent_apply f T h,heq]
      exact tsum_congr (fun i => by rw [hDaction,pushCurrent_apply f (C i).action h])
    · rw [show pushCurrent f T b π = 0 from ite_eq_right h]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π h)
        _ = 0 := tsum_zero

lemma integral_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2 hf hfJ⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2.1 hf hfJ,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push_of_bilipschitz hT.2.2.2 hf hfJ

end SharpIntegralFillings
namespace SharpIntegralFillings
universe u
theorem IsCAT0.closedBall {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) : IsCAT0 (Metric.closedBall o R) := by
  obtain ⟨s, hs, hd, hc⟩ := hX
  have hconv (x y : Metric.closedBall o R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      s x.val y.val t ∈ Metric.closedBall o R := by
    have hh := hc x.val y.val o t 1 ht (by simp)
    rw [(hs x.val o).2] at hh
    have he : (t * dist x.val y.val - 1 * dist x.val o) ^ 2 +
          t * 1 * (dist y.val o ^ 2 - (dist x.val y.val - dist x.val o) ^ 2) =
        (1 - t) * dist x.val o ^ 2 + t * dist y.val o ^ 2 -
          t * (1 - t) * dist x.val y.val ^ 2 := by ring
    rw [he] at hh
    have hx := (sq_le_sq₀ dist_nonneg hR).mpr x.property
    have hy := (sq_le_sq₀ dist_nonneg hR).mpr y.property
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)
    have hy' := mul_le_mul_of_nonneg_left hy ht.1
    have hh' : dist (s x.val y.val t) o ^ 2 ≤ R ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
        (sq_nonneg (dist x.val y.val))]
    exact (sq_le_sq₀ dist_nonneg hR).mp hh'
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclamp_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
    simp only [clamp, min_eq_right ht.2, max_eq_right ht.1]
  let sB : Metric.closedBall o R → Metric.closedBall o R → ℝ →
      Metric.closedBall o R := fun x y t => ⟨s x.val y.val (clamp t), hconv x y _ (hclamp t)⟩
  refine ⟨sB, ?_, ?_, ?_⟩
  · intro x y
    constructor <;> apply Subtype.ext
    · change s x.val y.val (clamp 0) = x.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).1]
    · change s x.val y.val (clamp 1) = y.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).2]
  · intro x y u v hu hv
    change dist (s x.val y.val (clamp u)) (s x.val y.val (clamp v)) = _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hd x.val y.val u v hu hv
  · intro p x y u v hu hv
    change dist (s p.val x.val (clamp u)) (s p.val y.val (clamp v)) ^ 2 ≤ _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hc p.val x.val y.val u v hu hv

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Currents_Negation
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [BorelSpace X] in
lemma controls_neg_iff {T : Functional X k} {μ : Measure X} :
    Controls (-T) μ ↔ Controls T μ := by
  simp only [Controls,Pi.neg_apply,abs_neg]

omit [BorelSpace X] in
lemma mass_neg (T : Functional X k) : mass (-T) = mass T := by
  simp only [mass,controls_neg_iff]

omit [BorelSpace X] in
lemma IsMetricCurrent.neg {T : Functional X k} (hT : IsMetricCurrent T) :
    IsMetricCurrent (-T) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [Pi.neg_apply,hT.offDomain b π hab,neg_zero]
  · intro b c π a d hb hc hπ
    simp only [Pi.neg_apply,hT.linearFirst b c π a d hb hc hπ]
    ring
  · intro b π i f a c hb hf
    simp only [Pi.neg_apply,hT.linearCoord b π i f a c hb hf]
    ring
  · intro b π πs hb hπ hlim
    exact (hT.sequentialContinuity b π πs hb hπ hlim).neg
  · intro b π hab hl
    simp only [Pi.neg_apply,hT.locality b π hab hl,neg_zero]
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    exact ⟨μ,hμ,controls_neg_iff.mpr hc⟩

namespace IntegerChart
variable (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] in
lemma negate_action : C.negate.action = -C.action := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · simp only [action,ite_eq_left hab,Pi.neg_apply]
    change (∫ z in C.domain,(-C.multiplicity z:ℤ)*C.scalar b z*C.jacobian π z) =
      -(∫ z in C.domain,(C.multiplicity z:ℝ)*C.scalar b z*C.jacobian π z)
    simp only [Int.cast_neg,neg_mul,integral_neg]
  · simp only [action,ite_eq_right hab,Pi.neg_apply,neg_zero]
end IntegerChart

omit [BorelSpace X] in
lemma IntegerRectifiable.neg {T : Functional X k} (hI : IntegerRectifiable T) :
    IntegerRectifiable (-T) := by
  obtain ⟨C,hd,hC,hS,heq⟩ := hI
  refine ⟨fun i => (C i).negate,hd,?_,?_,?_⟩
  · intro i
    rw [IntegerChart.negate_action]
    exact (hC i).neg
  · simp_rw [IntegerChart.negate_action,mass_neg]
    exact hS
  · intro b π
    simp only [IntegerChart.negate_action,Pi.neg_apply,heq,tsum_neg]

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallCurrent
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal RealInnerProductSpace

namespace SharpIntegralFillings

namespace Optimality

lemma innerSpace_CAT0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsCAT0 E := by
  let s : E → E → ℝ → E := fun x y t => (1-t) • x + t • y
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x y
    simp [s]
  · intro x y a b ha hb
    have he : s x y a - s x y b = (a-b) • (y-x) := by dsimp [s]; module
    simp only [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
    rw [norm_sub_rev y x]
  · intro o x y a b ha hb
    have he : s o x a - s o y b = a • (x-o) - b • (y-o) := by dsimp [s]; module
    have hi : ‖a • (x-o) - b • (y-o)‖^2 =
        a^2 * ‖x-o‖^2 + b^2 * ‖y-o‖^2 -
          a*b*(‖x-o‖^2 + ‖y-o‖^2 - ‖(x-o)-(y-o)‖^2) := by
      simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
      ring
    have hxy : (x-o)-(y-o) = x-y := by abel
    rw [hxy] at hi
    simp only [dist_eq_norm, he]
    rw [hi, norm_sub_rev o x, norm_sub_rev o y]
    nlinarith

lemma unitBall_CAT0 (d : ℕ) : IsCAT0 (UnitBall d) :=
  innerSpace_CAT0.closedBall 0 (by norm_num)

lemma chart_integerRectifiable {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {d : ℕ} (C : IntegerChart X d) : IntegerRectifiable C.action := by
  classical
  let D : ℕ → IntegerChart X d := fun i => if i = 0 then C else emptyChart d
  have hD (i : ℕ) : IsMetricCurrent (D i).action := (D i).action_isMetricCurrent
  refine ⟨D, ?_, hD, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by omega
      simp [D, hj]
    · simp [D, hi]
  · apply summable_of_ne_finset_zero (s := {0})
    intro i hi
    have hi' : i ≠ 0 := by simpa using hi
    simp [D, hi']
  · intro b π
    rw [tsum_eq_single 0]
    · simp [D]
    · intro i hi
      simp [D, hi]

lemma det_le_one_of_clm_norm {d : ℕ} (p : Fin d → Euc d →L[ℝ] ℝ)
    (hp : ∀ i, ‖p i‖ ≤ 1) :
    |Matrix.det (fun i j => p i (EuclideanSpace.single j 1))| ≤ 1 := by
  apply abs_det_le_one_of_dot_bound
  intro i v
  have hv : ∑ j, v j • EuclideanSpace.single j (1:ℝ) =
      (WithLp.toLp 2 v : Euc d) := by
    convert (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (WithLp.toLp 2 v) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have he : (fun j => p i (EuclideanSpace.single j 1)) ⬝ᵥ v =
      p i (WithLp.toLp 2 v) := by
    rw [← hv, map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  rw [he]
  exact (p i).le_opNorm _ |>.trans (by simpa using mul_le_mul_of_nonneg_right (hp i) (norm_nonneg (WithLp.toLp 2 v : Euc d)))

lemma chart_mass_le_unitLip {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X] {d : ℕ} (C : IntegerChart X d)
    (hC : LipschitzWith 1 C.param) :
    mass C.action ≤ ∫ z in C.domain, |(C.multiplicity z : ℝ)| := by
  let μ := C.majorantMeasure (fun _ => 1)
  have hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * 1)
      (volume.restrict C.domain) := by simpa using C.integrable.abs
  have hfin : IsFiniteMeasure μ := densityPush_finite _ _ hρ
  have hctrl : Controls C.action μ := by
    apply C.majorant_controls hρ (Eventually.of_forall fun _ => zero_le_one)
    intro π hπ
    have hnorm : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
        ‖fderivWithin ℝ (C.scalar (π i)) C.domain z‖ ≤ 1 := by
      apply ae_all_iff.mpr
      intro i
      have hs : LipschitzOnWith 1 (C.scalar (π i)) C.domain := by
        simpa only [one_mul] using C.scalar_lipschitzOn hC (hπ i)
      simpa using ae_norm_fderivWithin_le volume C.borel hs
    filter_upwards [hnorm] with z hz
    exact det_le_one_of_clm_norm _ hz
  apply (mass_le_measure hfin hctrl).trans_eq
  have hn : 0 ≤ᵐ[volume.restrict C.domain] fun z => |(C.multiplicity z : ℝ)| * 1 :=
    Eventually.of_forall fun z => by positivity
  have h := integral_densityPush (volume.restrict C.domain) C.measurable_paramExtended
    hρ hn (continuous_const : Continuous (fun _ : X => (1:ℝ)))
  simpa only [integral_const, smul_eq_mul, mul_one, IntegerChart.majorantMeasure, μ] using h

lemma ballChart_mass_le (d : ℕ) : mass (ballChart d).action ≤ omega d := by
  have hL : LipschitzWith 1 (ballChart d).param := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    rfl
  have h := chart_mass_le_unitLip (ballChart d) hL
  simpa [ballChart, omega, Measure.real] using h

end Optimality
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_SmoothCutoff
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
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.SmoothCutoff
lemma deriv_transition_eq_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  have hcases : x < 0 ∨ 1 < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
  rcases hcases with hx | hx
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq]
    simp
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq]
    simp

lemma tsupport_deriv_transition :
    tsupport (deriv Real.smoothTransition) ⊆ Icc (0:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (deriv_transition_eq_zero h)

lemma exists_derivative_bound : ∃ C : ℝ≥0, (∀ x, ‖deriv Real.smoothTransition x‖ ≤ C) ∧
    (∀ x, ‖deriv (deriv Real.smoothTransition) x‖ ≤ C) := by
  have hd : ContDiff ℝ (1:ℕ) (deriv Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff 2).deriv'
  have hc := hd.continuous
  have hc2 := hd.continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨⟨max 0 (max C D),le_max_left _ _⟩,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · exact (hC x hx).trans ((le_max_left C D).trans (le_max_right _ _))
    · rw [deriv_transition_eq_zero hx,norm_zero]
      exact le_max_left _ _
  · intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · exact (hD x hx).trans ((le_max_right C D).trans (le_max_right _ _))
    · have hz : deriv (deriv Real.smoothTransition) x = 0 := by
        exact deriv_of_notMem_tsupport (fun h => hx (tsupport_deriv_transition h))
      rw [hz,norm_zero]
      exact le_max_left _ _

lemma exists_lipschitz_transition : ∃ C : ℝ≥0, LipschitzWith C Real.smoothTransition ∧
    LipschitzWith C (deriv Real.smoothTransition) ∧
    ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C,hC,hD⟩ := exists_derivative_bound
  refine ⟨C,?_,?_,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num))
    exact fun x => hC x
  · apply lipschitzWith_of_nnnorm_deriv_le ((show ContDiff ℝ (1:ℕ) (deriv Real.smoothTransition) from (@Real.smoothTransition.contDiff 2).deriv').differentiable (by norm_num))
    exact fun x => hD x
  · simpa only [Real.norm_eq_abs] using hC

end SharpIntegralFillings.SmoothCutoff

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_Profiles
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
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.SmoothCutoff
open Set Filter
open scoped Topology NNReal

lemma affine_lipschitz (a : ℝ≥0) (t : ℝ) :
    LipschitzWith a (fun x : ℝ => (a:ℝ)*(x-t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,←mul_sub,sub_sub_sub_cancel_right,abs_mul,abs_of_nonneg a.coe_nonneg]
  exact le_rfl

lemma profile_hasDerivAt (a : ℝ≥0) (t x : ℝ) :
    HasDerivAt (profile a t) (dprofile a t x) x := by
  have hd := ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num) ((a:ℝ)*(x-t))).hasDerivAt
  change HasDerivAt (fun y => Real.smoothTransition ((a:ℝ)*(y-t)))
    ((a:ℝ)*deriv Real.smoothTransition ((a:ℝ)*(x-t))) x
  simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using
    hd.comp x (((hasDerivAt_id x).sub_const t).const_mul (a:ℝ))

lemma profile_bounds (a : ℝ≥0) (t x : ℝ) :
    0 ≤ profile a t x ∧ profile a t x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma profile_zero (a : ℝ≥0) {t x : ℝ} (hx : x ≤ t) : profile a t x = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos a.coe_nonneg (sub_nonpos.mpr hx))

lemma dprofile_zero {a : ℝ≥0} (ha : 0 < a) {t x : ℝ}
    (hx : x ∉ Icc t (t+(a:ℝ)⁻¹)) : dprofile a t x = 0 := by
  have ha' : 0 < (a:ℝ) := ha
  have hnot : (a:ℝ)*(x-t) ∉ Icc 0 1 := by
    intro h
    apply hx
    refine ⟨?_,?_⟩
    · have : 0 ≤ x-t := (mul_nonneg_iff_of_pos_left ha').mp h.1
      linarith
    · have : x-t ≤ (a:ℝ)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ ha').mpr
        simpa [mul_comm] using h.2
      linarith
  simp [dprofile,deriv_transition_eq_zero hnot]

lemma exists_profile_bounds : ∃ C : ℝ≥0, ∀ (a : ℝ≥0) (t : ℝ),
    LipschitzWith (C*a) (profile a t) ∧
    LipschitzWith (a*(C*a)) (dprofile a t) ∧
    ∀ x, |dprofile a t x| ≤ (C*a:ℝ≥0) := by
  obtain ⟨C,hC,hD,hb⟩ := exists_lipschitz_transition
  refine ⟨C,fun a t => ⟨hC.comp (affine_lipschitz a t),?_,?_⟩⟩
  · change LipschitzWith (a*(C*a)) (fun x => (a:ℝ)*deriv Real.smoothTransition ((a:ℝ)*(x-t)))
    simpa only [sub_zero,Function.comp_def] using
      (affine_lipschitz a 0).comp (hD.comp (affine_lipschitz a t))
  · intro x
    simp only [dprofile,abs_mul,abs_of_nonneg a.coe_nonneg,NNReal.coe_mul]
    calc
      (a:ℝ) * |deriv Real.smoothTransition ((a:ℝ)*(x-t))| ≤ (a:ℝ)*C :=
        mul_le_mul_of_nonneg_left (hb _) a.coe_nonneg
      _ = (C:ℝ)*a := mul_comm _ _

lemma profile_sequence_tendsto (t x : ℝ) :
    Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) t x) atTop
      (𝓝 ((Ioi t).indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : t < x
  · rw [indicator_of_mem (show x ∈ Ioi t from hx)]
    have hlim : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(x-t)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const (sub_pos.mpr hx)
    have heq : (fun n : ℕ => profile ((n:ℝ≥0)+1) t x) =ᶠ[atTop] fun _ => (1:ℝ) := by
      filter_upwards [hlim.eventually (eventually_ge_atTop 1)] with n hn
      apply Real.smoothTransition.one_of_one_le
      simpa only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hn
    exact tendsto_const_nhds.congr' heq.symm
  · rw [indicator_of_notMem (show x ∉ Ioi t from hx)]
    simpa only [profile_zero _ (le_of_not_gt hx)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end SharpIntegralFillings.SmoothCutoff
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_NormalRestriction
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
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace SharpIntegralFillings.Slicing
open Set MeasureTheory Filter BorelCoefficients BorelRestriction MassMeasure SmoothCutoff
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma profile_comp_boundedLip {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) (t : ℝ) : BoundedLip (profile a t ∘ u) := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  refine ⟨⟨_,(hC a t).1.comp hK⟩,1,fun x => ?_⟩
  change |profile a t (u x)| ≤ 1
  rw [abs_of_nonneg (profile_bounds a t (u x)).1]
  exact (profile_bounds a t (u x)).2

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma dprofile_comp_boundedLip {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) (t : ℝ) : BoundedLip (dprofile a t ∘ u) := by
  obtain ⟨K,hK⟩ := hu.1
  obtain ⟨C,hC⟩ := exists_profile_bounds
  refine ⟨⟨_,(hC a t).2.1.comp hK⟩,(C*a:ℝ≥0),fun x => ?_⟩
  exact (hC a t).2.2 (u x)

lemma profile_L1_tendsto (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ}
    (hu : BoundedLip u) (t : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, |profile ((n:ℝ≥0)+1) t (u x) -
      ({x | t < u x}.indicator (fun _ => (1:ℝ)) x)| ∂μ) atTop (𝓝 0) := by
  let E : Set X := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.continuous.measurable
  have hI : Integrable (E.indicator (fun _ : X => (1:ℝ))) μ :=
    (integrable_const _).indicator hE
  have hP (n : ℕ) : Integrable (fun x => profile ((n:ℝ≥0)+1) t (u x)) μ :=
    integrable_boundedLip μ (profile_comp_boundedLip hu _ t)
  have hpt (x : X) : Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) t (u x)) atTop
      (𝓝 (E.indicator (fun _ => (1:ℝ)) x)) := by
    simpa only [E,indicator_apply,mem_Ioi,mem_ofPred_eq] using profile_sequence_tendsto t (u x)
  have hdom (n : ℕ) : ∀ᵐ x ∂μ,
      ‖|profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x|‖ ≤ (2:ℝ) := by
    filter_upwards [] with x
    have hp := profile_bounds ((n:ℝ≥0)+1) t (u x)
    have hi : 0 ≤ E.indicator (fun _ => (1:ℝ)) x ∧ E.indicator (fun _ => (1:ℝ)) x ≤ 1 := by
      by_cases hx : x ∈ E <;> simp [hx]
    simpa only [Real.norm_eq_abs,abs_abs] using
      (abs_le.mpr (show -2 ≤ profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x ∧
        profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x ≤ 2 from by
          constructor <;> linarith [hp.1,hp.2,hi.1,hi.2]))
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => |profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x|)
    (f := fun _ => (0:ℝ)) (fun _ => (2:ℝ))
    (fun n => ((hP n).sub hI).abs.aestronglyMeasurable) (integrable_const _) hdom
    (Eventually.of_forall fun x => by
      simpa only [sub_self,abs_zero] using ((hpt x).sub (tendsto_const_nhds (x := E.indicator (fun _ => (1:ℝ)) x))).abs)
  simpa only [integral_zero] using h

lemma profile_boundary_tendsto {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
    Tendsto (fun n : ℕ => boundarySucc (weightedCurrent (currentMassMeasure hT) hT
      (profile ((n:ℝ≥0)+1) t ∘ u)) b π) atTop
      (𝓝 (boundarySucc (restrictCurrent hT {x | t < u x}) b π)) := by
  let μ := currentMassMeasure hT
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.continuous.measurable
  have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
    ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
  simp only [boundarySucc,ite_eq_left hab,weightedCurrent,ite_eq_left hcons,mul_one,
    restrictCurrent,Function.comp_apply]
  exact borelAction_tendsto μ hT (currentMassMeasure_controls hT)
    ((integrable_const _).indicator hE)
    (fun n => integrable_boundedLip μ (profile_comp_boundedLip hu _ t))
    (profile_L1_tendsto μ hu t) (Matrix.vecCons b π) hcons.2

end SharpIntegralFillings.Slicing
open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallStokes
attribute [-simp] _root_.OAI.SharpIntegralFillings.EuclideanStraightening.replaceMap_apply _root_.OAI.SharpIntegralFillings.EuclideanStraightening.straightenMap_zero _root_.OAI.SharpIntegralFillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open SmoothCutoff

lemma radiusFunction_lipschitz (d : ℕ) : LipschitzWith 1 (radiusFunction d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [radiusFunction, NNReal.coe_one, one_mul, dist_neg_neg, Real.dist_eq,
    Subtype.dist_eq]
  rw [dist_eq_norm]
  exact abs_norm_sub_norm_le x.val y.val

lemma radiusFunction_boundedLip (d : ℕ) : BoundedLip (radiusFunction d) := by
  refine ⟨⟨1, radiusFunction_lipschitz d⟩, 1, ?_⟩
  intro x
  simpa only [radiusFunction, abs_neg, abs_of_nonneg (norm_nonneg _),
    Metric.mem_closedBall, dist_zero_right] using x.property

lemma radialProfile_contDiff {d : ℕ} {a : ℝ≥0} {t : ℝ}
    (ha : 1 < (a:ℝ) * (-t)) : ContDiff ℝ 1 (radialProfile (d := d) a t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hc : Continuous (fun z : Euc d => (a:ℝ) * (-‖z‖ - t)) := by fun_prop
    have he : radialProfile (d := d) a t =ᶠ[𝓝 0] fun _ => 1 := by
      have ha' : 1 < (a:ℝ) * (-‖(0 : Euc d)‖ - t) := by simpa using ha
      filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds ha')] with z hz
      exact Real.smoothTransition.one_of_one_le hz.le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact Real.smoothTransition.contDiff.contDiffAt.comp x
      (contDiffAt_const.mul ((contDiffAt_id.norm ℝ hx).neg.sub contDiffAt_const))

lemma radialProfile_compact {d : ℕ} (a : ℝ≥0) (t : ℝ) :
    HasCompactSupport (radialProfile (d := d) a t) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (-t))
  intro x hx
  apply profile_zero
  have hh : -t < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  linarith

lemma radialProfile_zero_outside {d : ℕ} (a : ℝ≥0) {t : ℝ} (ht : -1 < t)
    {x : Euc d} (hx : x ∉ Metric.ball 0 1) : radialProfile a t x = 0 := by
  apply profile_zero
  have hh : 1 ≤ ‖x‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  linarith

lemma radialProfile_fderiv_zero_outside {d : ℕ} (a : ℝ≥0) {t : ℝ} (ht : -1 < t)
    {x : Euc d} (hx : x ∉ Metric.ball 0 1) : fderiv ℝ (radialProfile a t) x = 0 := by
  have hh : 1 ≤ ‖x‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx
  have he : radialProfile a t =ᶠ[𝓝 x] fun _ => 0 := by
    have hc : Continuous (fun y : Euc d => -‖y‖) := continuous_norm.neg
    have hx' : -‖x‖ < t := by linarith
    filter_upwards [hc.continuousAt.eventually_lt_const hx'] with y hy
    exact profile_zero a hy.le
  simpa using he.fderiv_eq (𝕜 := ℝ)

lemma ballChart_param_lipschitz (d : ℕ) : LipschitzWith 1 (ballChart d).param := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  rfl

lemma ballChart_scalar_extension {d : ℕ} {f : UnitBall d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ F : Euc d → ℝ, LipschitzWith K F ∧ EqOn ((ballChart d).scalar f) F (ballChart d).domain := by
  have hs : LipschitzOnWith K ((ballChart d).scalar f) (ballChart d).domain := by
    simpa using (ballChart d).scalar_lipschitzOn (ballChart_param_lipschitz d) hf
  exact hs.extend_real

lemma ballChart_action_extensions {d : ℕ} {b : UnitBall d → ℝ}
    {π : Fin d → UnitBall d → ℝ} {B : Euc d → ℝ} {P : Fin d → Euc d → ℝ}
    {K : Fin d → ℝ≥0} (hab : Admissible b π) (hP : ∀ i, LipschitzWith (K i) (P i))
    (hb : EqOn ((ballChart d).scalar b) B (ballChart d).domain)
    (hπ : ∀ i, EqOn ((ballChart d).scalar (π i)) (P i) (ballChart d).domain) :
    (ballChart d).action b π = ∫ z in Metric.ball 0 1,
      B z * coordinateJacobian P (fun j => EuclideanSpace.single j 1) z := by
  rw [IntegerChart.action, ite_eq_left hab]
  apply integral_congr_ae
  filter_upwards [(ballChart d).ae_jacobian_eq_extensions hP hπ,
    ae_restrict_mem (ballChart d).borel] with z hj hz
  change (1:ℤ) * ((ballChart d).scalar b z) * _ = _
  rw [Int.cast_one, one_mul, hb hz, hj]
  congr 1
  rw [coordinateJacobian, ← Matrix.det_transpose]
  rfl

lemma radialProfile_lipschitz {d : ℕ} (a : ℝ≥0) (t : ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (radialProfile (d := d) a t) := by
  obtain ⟨C, hC⟩ := exists_profile_bounds
  have hn : LipschitzWith 1 (fun z : Euc d => -‖z‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_neg_neg, Real.dist_eq]
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  exact ⟨C*a*1, (hC a t).1.comp hn⟩

lemma ballChart_local_stokes {k : ℕ} {a : ℝ≥0} {t : ℝ} (ht : -1 < t)
    (ha : 1 < (a:ℝ) * (-t)) {b : UnitBall (k+1) → ℝ}
    {π : Fin k → UnitBall (k+1) → ℝ} (hab : Admissible b π) :
    (ballChart (k+1)).action (profile a t ∘ radiusFunction (k+1)) (Matrix.vecCons b π) =
      -(ballChart (k+1)).action b (Matrix.vecCons (profile a t ∘ radiusFunction (k+1)) π) := by
  let C := ballChart (k+1)
  let f := radialProfile (d := k+1) a t
  obtain ⟨K, hK⟩ := hab.1.1
  obtain ⟨B, hB, hBe⟩ := ballChart_scalar_extension hK
  choose L hL using hab.2
  choose P hP hPe using fun i => ballChart_scalar_extension (hL i)
  obtain ⟨J,hJ⟩ := radialProfile_lipschitz (d := k+1) a t
  have hprof := Slicing.profile_comp_boundedLip (radiusFunction_boundedLip (k+1)) a t
  have hfe : EqOn (C.scalar (profile a t ∘ radiusFunction (k+1))) f C.domain := by
    intro z hz
    rw [C.scalar_eq hz]
    rfl
  have hleft : C.action (profile a t ∘ radiusFunction (k+1)) (Matrix.vecCons b π) =
      ∫ z in Metric.ball 0 1, f z * coordinateJacobian (Fin.cons B P)
        (fun j => EuclideanSpace.single j 1) z := by
    apply ballChart_action_extensions (K := Fin.cons K L)
      (Foundations.admissible_vecCons hprof hab.1.1 hab.2)
    · intro i
      exact Fin.cases hB (fun j => hP j) i
    · exact hfe
    · intro i
      exact Fin.cases hBe (fun j => hPe j) i
  have hright : C.action b (Matrix.vecCons (profile a t ∘ radiusFunction (k+1)) π) =
      ∫ z in Metric.ball 0 1, B z * coordinateJacobian (Fin.cons f P)
        (fun j => EuclideanSpace.single j 1) z := by
    apply ballChart_action_extensions (K := Fin.cons J L)
      (Foundations.admissible_vecCons hab.1 hprof.1 hab.2)
    · intro i
      exact Fin.cases hJ (fun j => hP j) i
    · exact hBe
    · intro i
      exact Fin.cases hfe (fun j => hPe j) i
  rw [hleft, hright]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · have hPu : ∀ i, LipschitzWith (∑ j, L j) (P i) := fun i =>
        (hP i).weaken (Finset.single_le_sum (fun j _ => zero_le) (Finset.mem_univ i))
      exact integral_coordinateJacobian_cons volume (radialProfile_contDiff ha)
        (radialProfile_compact a t) hB hPu (fun j => EuclideanSpace.single j 1)
    · have hdf : fderiv ℝ f z = 0 := radialProfile_fderiv_zero_outside a ht hz
      have hdet : coordinateJacobian (Fin.cons f P) (fun j => EuclideanSpace.single j 1) z = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero 0
        intro i
        change fderiv ℝ f z _ = 0
        rw [hdf]
        rfl
      rw [hdet, mul_zero]
  · rw [show f z = 0 from radialProfile_zero_outside a ht hz, zero_mul]

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_BoundaryTests
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite
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
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.Foundations
open Set MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [BorelSpace X] in
lemma IsMetricCurrent.boundary_testClass_continuous {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (K : ℕ) :
    Continuous (TestClass.eval (X := X) (K := K) (boundarySucc T)) := by
  apply continuous_iff_seqContinuous.mpr
  intro ps p hp
  have had (q : TestClass (X := X) k K) : Admissible (q.val.1 : X → ℝ) (fun i => q.val.2 i) :=
    ⟨q.boundedLip,fun i => ⟨K,q.property.2.2 i⟩⟩
  simp only [Function.comp_def,TestClass.eval,boundarySucc,ite_eq_left (had _)]
  apply hT.sequentialContinuity _ _ _ (BoundedLip.const 1)
  · intro i
    exact ⟨K,fun n => Fin.cases (ps n).property.1 (fun j => (ps n).property.2.2 j) i⟩
  · intro i x
    refine Fin.cases ?_ (fun j => ?_) i
    · have hc : Continuous (fun q : TestClass (X := X) k K => q.val.1 x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp
    · have hc : Continuous (fun q : TestClass (X := X) k K => q.val.2 j x) := by fun_prop
      exact hc.continuousAt.tendsto.comp hp

theorem ae_boundary_eq_of_ae_test_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {S : A → Functional X (k+1)} {T : A → Functional X k}
    (hS : ∀ᵐ a ∂μ, IsMetricCurrent (S a)) (hT : ∀ᵐ a ∂μ, IsMetricCurrent (T a))
    (he : ∀ b π, Admissible b π → ∀ᵐ a ∂μ, boundarySucc (S a) b π = T a b π) :
    ∀ᵐ a ∂μ, boundarySucc (S a) = T a := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (TestClass (X := X) k K)
  have ha K j : Admissible ((p K j).val.1 : X → ℝ) (fun i => (p K j).val.2 i) :=
    ⟨(p K j).boundedLip,fun i => ⟨K,(p K j).property.2.2 i⟩⟩
  have hc : ∀ᵐ a ∂μ, ∀ K j, TestClass.eval (boundarySucc (S a)) (p K j) = TestClass.eval (T a) (p K j) :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => he _ _ (ha K j)
  filter_upwards [hS,hT,hc] with a hs ht h
  have hh K : TestClass.eval (K := K) (boundarySucc (S a)) = TestClass.eval (K := K) (T a) := by
    apply (hp K).equalizer (IsMetricCurrent.boundary_testClass_continuous hs K) (IsMetricCurrent.testClass_continuous ht K)
    funext j; exact h K j
  funext b π
  by_cases hab : Admissible b π
  · obtain ⟨K,q,hb,hπ⟩ := admissible_mem_testClass hab
    have hz := congrFun (hh K) q
    simpa only [TestClass.eval,hb,hπ] using hz
  · rw [ht.offDomain b π hab,boundarySucc,ite_eq_right hab]

end SharpIntegralFillings.Foundations
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_ProfileIntegral
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
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.SmoothCutoff
open Set MeasureTheory Filter Metric
open scoped Topology NNReal

lemma dprofile_integrable {a : ℝ≥0} (ha : 0 < a) (t : ℝ) :
    Integrable (dprofile a t) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  have hc := (hC a t).2.1.continuous
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro isCompact_Icc
  exact fun x hx => dprofile_zero ha hx

lemma integral_dprofile {a : ℝ≥0} (ha : 0 < a) (t : ℝ) :
    (∫ x : ℝ, dprofile a t x) = 1 := by
  have ha' : 0 < (a:ℝ) := ha
  obtain ⟨C,hC⟩ := exists_profile_bounds
  have hc := (hC a t).2.1.continuous
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => dprofile_zero ha hx),
    integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show t ≤ t+(a:ℝ)⁻¹ from le_add_of_nonneg_right (inv_nonneg.mpr ha'.le)),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => profile_hasDerivAt a t x)
      (hc.intervalIntegrable _ _)]
  simp [profile,ha'.ne',Real.smoothTransition.one_of_one_le]

lemma dprofile_mul_integrable {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ≥0) (t : ℝ) :
    Integrable (fun x => dprofile a t x * f x) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  exact hf.bdd_mul (hC a t).2.1.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hC a t).2.2 x)

theorem ae_tendsto_dprofile_integral {f : ℝ → ℝ} (hf : Integrable f) :
    ∀ᵐ t : ℝ, Tendsto (fun n : ℕ => ∫ x : ℝ,
      dprofile ((n:ℝ≥0)+1) t x * f x) atTop (𝓝 (f t)) := by
  obtain ⟨C,hC⟩ := exists_profile_bounds
  let a : ℕ → ℝ≥0 := fun n => (n:ℝ≥0)+1
  let r : ℕ → ℝ := fun n => ((a n:ℝ))⁻¹
  have hap n : 0 < a n := by dsimp [a] <;> positivity
  have harp n : 0 < (a n:ℝ) := hap n
  have hrp n : 0 < r n := inv_pos.mpr (harp n)
  have hrt : Tendsto r atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall fun n => hrp n⟩
    exact tendsto_inv_atTop_zero.comp
      (show Tendsto (fun n : ℕ => (a n:ℝ)) atTop atTop from by
        simpa only [a,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
          tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hf.locallyIntegrable 0]
    with t ht
  have hav := ht (fun _ : ℕ => t) r hrt
    (Eventually.of_forall fun n => by simp only [zero_mul]; exact mem_closedBall_self le_rfl)
  have hbound n : ‖(∫ x : ℝ, dprofile (a n) t x * f x)-f t‖ ≤
      (2*(C:ℝ)) * (⨍ x in closedBall t (r n), ‖f x-f t‖) := by
    have hk := dprofile_integrable (hap n) t
    have hprod := dprofile_mul_integrable hf (a n) t
    have heq : (∫ x : ℝ, dprofile (a n) t x * f x)-f t =
        ∫ x : ℝ, dprofile (a n) t x * (f x-f t) := by
      simp only [mul_sub,integral_sub hprod (hk.mul_const _),integral_mul_const,
        integral_dprofile (hap n),one_mul]
    rw [heq]
    have herr : Integrable (fun x : ℝ => dprofile (a n) t x * (f x-f t)) := by
      apply (hprod.sub (hk.mul_const (f t))).congr
      filter_upwards [] with x
      exact (mul_sub _ _ _).symm
    have hnz (x : ℝ) (hx : x ∉ closedBall t (r n)) : dprofile (a n) t x = 0 := by
      apply dprofile_zero (hap n)
      intro hi
      apply hx
      rw [Real.closedBall_eq_Icc]
      change t-r n ≤ x ∧ x ≤ t+r n
      exact ⟨by linarith [hi.1,hrp n],hi.2⟩
    have hloc : IntegrableOn (fun x : ℝ => ‖f x-f t‖) (closedBall t (r n)) :=
      (hf.integrableOn.sub (integrableOn_const (measure_closedBall_lt_top.ne))).norm
    calc
      ‖∫ x : ℝ, dprofile (a n) t x * (f x-f t)‖ ≤
          ∫ x : ℝ, ‖dprofile (a n) t x * (f x-f t)‖ := norm_integral_le_integral_norm _
      _ = ∫ x in closedBall t (r n), ‖dprofile (a n) t x * (f x-f t)‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hnz x hx,zero_mul,norm_zero])).symm
      _ ≤ ∫ x in closedBall t (r n), ((C:ℝ)*(a n:ℝ)) * ‖f x-f t‖ := by
        apply setIntegral_mono_on herr.norm.integrableOn (hloc.const_mul _) isClosed_closedBall.measurableSet
        intro x _
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Real.norm_eq_abs,NNReal.coe_mul] using (hC (a n) t).2.2 x
      _ = (2*(C:ℝ)) * (⨍ x in closedBall t (r n), ‖f x-f t‖) := by
        rw [integral_const_mul,setAverage_eq,Real.volume_real_closedBall (hrp n).le,
          smul_eq_mul]
        dsimp [r]
        field_simp
  have hzero := squeeze_zero_norm hbound (by simpa only [mul_zero] using hav.const_mul (2*(C:ℝ)))
  simpa only [sub_add_cancel,zero_add] using hzero.add_const (f t)

end SharpIntegralFillings.SmoothCutoff
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Slicing_RectifiableCoarea
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
open Set MeasureTheory Filter BorelRestriction MassMeasure
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}
lemma chartFamily_restrict_eq {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π) (i : ℕ) :
    restrictCurrent hT (C i).image = (C i).action := by
  funext b π
  rw [restrictCurrent_sum hT hC hsum heq (C i).measurableSet_image,
    tsum_eq_single i (fun j hj => by
      rw [(C j).restrictCurrent_disjoint_eq_zero (hC j) (C i).measurableSet_image (hd hj)]
      rfl),
    (C i).restrictCurrent_image_eq (hC i) (C i).measurableSet_image (subset_refl _)]

lemma chartFamily_mass_sum_le {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action)
    (hsum : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π) :
    (∑' i, mass (C i).action) ≤ mass T := by
  have hr i := chartFamily_restrict_eq hT C hd hC hsum heq i
  simpa only [hr] using tsum_restriction_mass_le hT (fun i => (C i).image)
    (fun i => (C i).measurableSet_image) hd

theorem integerRectifiable_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hI : ∀ i, IntegerRectifiable (T i))
    (hsum : Summable (fun i => mass (T i))) :
    IntegerRectifiable (fun b π => ∑' i, T i b π) := by
  choose C hd hC hCS heq using hI
  have hmass i := chartFamily_mass_sum_le (hT i) (C i) (hd i) (hC i) (hCS i) (heq i)
  have hpair : Summable (fun p : ℕ × ℕ => mass (C p.1 p.2).action) := by
    apply (summable_prod_of_nonneg (fun p => mass_nonneg _)).mpr
    exact ⟨hCS,hsum.of_nonneg_of_le (fun i => tsum_nonneg (fun j => mass_nonneg _)) hmass⟩
  let D (i : ℕ) := C (Nat.pairEquiv.symm i).1 (Nat.pairEquiv.symm i).2
  have hD i : IsMetricCurrent (D i).action := hC _ _
  have hDS : Summable (fun i => mass (D i).action) := (Nat.pairEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => mass (C p.1 p.2).action)).mpr hpair
  have heq' : (fun b π => ∑' i, T i b π) = (fun b π => ∑' i, (D i).action b π) := by
    funext b π
    have hact : Summable (fun p : ℕ × ℕ => (C p.1 p.2).action b π) :=
      (Nat.pairEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => (C p.1 p.2).action b π)).mp (summable_actions_all hD hDS b π)
    change (∑' i, T i b π) = ∑' i, (C (Nat.pairEquiv.symm i).1 (Nat.pairEquiv.symm i).2).action b π
    calc
      (∑' i, T i b π) = ∑' i, ∑' j, (C i j).action b π := tsum_congr (fun i => heq i b π)
      _ = ∑' p : ℕ × ℕ, (C p.1 p.2).action b π := hact.tsum_prod.symm
      _ = _ := (Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => (C p.1 p.2).action b π)).symm
  rw [heq']
  exact integerRectifiable_chartSum D hD hDS

end SharpIntegralFillings
namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem integerRectifiable_scalar_coarea {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ (S : ℝ → Functional X k) (G : ℝ → ℝ),
      Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∀ᵐ t : ℝ, IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass T ∧
      (∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
        T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π) ∧
      (∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
        ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) := by
  obtain ⟨C,hd,hC,hCS,heq⟩ := hI
  have hmass := chartFamily_mass_sum_le hT C hd hC hCS heq
  choose Q G hG hG0 hQ hGI hQact hQweight using fun i => (C i).exists_scalar_coarea hX hK
  let S : ℝ → Functional X k := fun t b π => ∑' i, Q i t b π
  have hGIs : Summable (fun i => ∫ t : ℝ, G i t) := by
    apply (hCS.mul_left (K:ℝ)).of_nonneg_of_le
      (fun i => integral_nonneg (hG0 i)) hGI
  have hGn : Summable (fun i => ∫ t : ℝ, ‖G i t‖) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using hGIs
  have hGa : ∀ᵐ t : ℝ, Summable (fun i => G i t) := by
    simpa only [Real.norm_of_nonneg (hG0 _ _)] using ae_summable_norm_of_integral hG hGn
  have hQa : ∀ᵐ t : ℝ, Summable (fun i => mass (Q i t)) := by
    filter_upwards [hGa,ae_all_iff.mpr hQ] with t hs hm
    exact hs.of_nonneg_of_le (fun i => mass_nonneg _) (fun i => (hm i).2.2)
  refine ⟨S,fun t => ∑' i, G i t,integrable_series hG hGn,
    fun t => tsum_nonneg (fun i => hG0 i t),?_,?_,?_,?_⟩
  · filter_upwards [hQa,hGa,ae_all_iff.mpr hQ] with t hqt hgt hmt
    refine ⟨isMetricCurrent_tsum (fun i => (hmt i).1) hqt,
      integerRectifiable_tsum (fun i => (hmt i).1) (fun i => (hmt i).2.1) hqt,?_⟩
    exact (mass_tsum_le (fun i => (hmt i).1) hqt).trans
      (hqt.tsum_le_tsum (fun i => (hmt i).2.2) hgt)
  · rw [←integral_tsum_of_summable_integral_norm hG hGn]
    calc
      (∑' i, ∫ t : ℝ, G i t) ≤ ∑' i, (K:ℝ)*mass (C i).action :=
        hGIs.tsum_le_tsum hGI (hCS.mul_left _)
      _ = (K:ℝ)*(∑' i, mass (C i).action) := tsum_mul_left
      _ ≤ (K:ℝ)*mass T := mul_le_mul_of_nonneg_left hmass K.coe_nonneg
  · intro b π hab
    have hi i : Integrable (fun t : ℝ => Q i t b π) := (hQact i b π hab).1
    choose L hL using hab.2
    obtain ⟨M,hM⟩ := hab.1.2
    let A : ℝ := (∏ j, (L j:ℝ)) * max M 0
    have hA : 0 ≤ A := mul_nonneg (Finset.prod_nonneg fun j _ => (L j).coe_nonneg) (le_max_right _ _)
    have hbound i : ∀ᵐ t : ℝ, ‖Q i t b π‖ ≤ A * G i t := by
      filter_upwards [hQ i] with t ht
      rw [Real.norm_eq_abs]
      exact (ht.1.mass_bound_uniform hab.1 L hL
        (fun x => (hM x).trans (le_max_left _ _))).trans
          (mul_le_mul_of_nonneg_left ht.2.2 hA)
    have hIs : Summable (fun i => ∫ t : ℝ, ‖Q i t b π‖) := by
      apply (hGIs.mul_left A).of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _))
      intro i
      rw [←integral_const_mul]
      exact integral_mono_ae (hi i).norm ((hG i).const_mul A) (hbound i)
    refine ⟨integrable_series hi hIs,?_⟩
    rw [heq]
    simp_rw [fun i => (hQact i b π hab).2]
    exact integral_tsum_of_summable_integral_norm hi hIs
  · intro b π hab φ hφ
    filter_upwards [ae_all_iff.mpr (fun i => hQweight i b π hab φ hφ)] with t ht
    change (∑' i, Q i t (fun x => φ (u x)*b x) π) = φ t * ∑' i, Q i t b π
    exact (tsum_congr fun i => ht i).trans tsum_mul_left

end SharpIntegralFillings

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

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallCoarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open SmoothCutoff Slicing BorelCoefficients BorelRestriction MassMeasure

lemma innerBallCurrent_metric (d : ℕ) (t : ℝ) : IsMetricCurrent (innerBallCurrent d t) :=
  restrictCurrent_isMetricCurrent (ballChart d).action_isMetricCurrent
    (measurableSet_lt measurable_const (radiusFunction_lipschitz d).continuous.measurable)

lemma innerBallCurrent_rectifiable (d : ℕ) (t : ℝ) : IntegerRectifiable (innerBallCurrent d t) :=
  integerRectifiable_restrict (ballChart d).action_isMetricCurrent
    (chart_integerRectifiable _) (measurableSet_lt measurable_const
      (radiusFunction_lipschitz d).continuous.measurable)

lemma ball_boundary_profile_coarea {k : ℕ} {S : ℝ → Functional (UnitBall (k+1)) k}
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      (ballChart (k+1)).action b (Matrix.vecCons (radiusFunction (k+1)) π) =
        ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ,
      BoundedLip (φ ∘ radiusFunction (k+1)) →
      ∀ᵐ t : ℝ, S t (fun x => φ (radiusFunction (k+1) x)*b x) π = φ t * S t b π)
    {a : ℝ≥0} {t : ℝ} (ht : -1 < t) (ha : 1 < (a:ℝ)*(-t))
    {b : UnitBall (k+1) → ℝ} {π : Fin k → UnitBall (k+1) → ℝ} (hab : Admissible b π) :
    boundarySucc (weightedCurrent (currentMassMeasure (ballChart (k+1)).action_isMetricCurrent)
      (ballChart (k+1)).action_isMetricCurrent (profile a t ∘ radiusFunction (k+1))) b π =
      -(∫ s : ℝ, dprofile a t s * S s b π) := by
  let C := ballChart (k+1)
  have hT := C.action_isMetricCurrent
  have hI := chart_integerRectifiable C
  have hu := radiusFunction_boundedLip (k+1)
  have hprof := profile_comp_boundedLip hu a t
  have hcons := Foundations.admissible_vecCons (BoundedLip.const 1) hab.1.1 hab.2
  simp only [boundarySucc, ite_eq_left hab, weightedCurrent, ite_eq_left hcons, mul_one]
  rw [borelAction_eq _ hT (currentMassMeasure_controls hT)
    (Foundations.admissible_vecCons hprof hab.1.1 hab.2)]
  rw [ballChart_local_stokes ht ha hab]
  congr 1
  have hπ' := (Foundations.admissible_vecCons hab.1 hu.1 hab.2).2
  have hchain := Foundations.IntegerRectifiable.apply_update_comp hI hab.1 hu
    (profile_hasDerivAt a t) (profile_comp_boundedLip hu a t)
    (dprofile_comp_boundedLip hu a t) (Matrix.vecCons (radiusFunction (k+1)) π) hπ' 0
  simp only [vecCons_update_head] at hchain
  rw [hchain]
  have heq : (fun x => b x*dprofile a t (radiusFunction (k+1) x)) =
      (fun x => dprofile a t (radiusFunction (k+1) x)*b x) := by funext x; ring
  rw [heq]
  trans ∫ s : ℝ, S s (fun x => dprofile a t (radiusFunction (k+1) x)*b x) π
  · exact (hact _ π ⟨(dprofile_comp_boundedLip hu a t).mul hab.1, hab.2⟩).2
  exact integral_congr_ae (hweight b π hab (dprofile a t) (dprofile_comp_boundedLip hu a t))

lemma eventually_profile_smooth (t : ℝ) (ht : t < 0) :
    ∀ᶠ n : ℕ in atTop, 1 < ((n:ℝ)+1)*(-t) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/(-t))
  have ht' : 0 < -t := neg_pos.mpr ht
  have hN' := (div_lt_iff₀ ht').mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_le_mul_of_nonneg_right hn' ht'.le]

theorem innerBall_ae_integral (k : ℕ) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ omega (k+1) ∧
      ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
        IsIntegral (k+1) (innerBallCurrent (k+1) t) ∧
        mass (boundarySucc (innerBallCurrent (k+1) t)) ≤ G t := by
  let C := ballChart (k+1)
  have hT := C.action_isMetricCurrent
  have hI := chart_integerRectifiable C
  have hu := radiusFunction_boundedLip (k+1)
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea
    hT hI (unitBall_CAT0 (k+1)) (radiusFunction_lipschitz (k+1))
  have hs : ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
      IsMetricCurrent (S t) ∧ IntegerRectifiable (S t) ∧ mass (S t) ≤ G t :=
    hS.filter_mono (ae_mono Measure.restrict_le_self)
  have htest (b : UnitBall (k+1) → ℝ) (π : Fin k → UnitBall (k+1) → ℝ)
      (hab : Admissible b π) :
      ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
        boundarySucc (innerBallCurrent (k+1) t) b π = (-S t) b π := by
    have hh := (ae_tendsto_dprofile_integral (hact b π hab).1).filter_mono
      (ae_mono (Measure.restrict_le_self (s := Ioo (-1:ℝ) 0)))
    filter_upwards [hh, ae_restrict_mem measurableSet_Ioo] with t ht hti
    have hl := profile_boundary_tendsto hT hu t b π hab
    have he : ∀ᶠ n : ℕ in atTop,
        boundarySucc (weightedCurrent (currentMassMeasure hT) hT
          (profile ((n:ℝ≥0)+1) t ∘ radiusFunction (k+1))) b π =
          -(∫ s : ℝ, dprofile ((n:ℝ≥0)+1) t s * S s b π) := by
      filter_upwards [eventually_profile_smooth t hti.2] with n hn
      apply ball_boundary_profile_coarea hact hweight hti.1 _ hab
      simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hn
    exact tendsto_nhds_unique (hl.congr' he) ht.neg
  have heq : ∀ᵐ t ∂volume.restrict (Ioo (-1:ℝ) 0),
      boundarySucc (innerBallCurrent (k+1) t) = -S t :=
    Foundations.ae_boundary_eq_of_ae_test_eq _
      (Eventually.of_forall fun t => innerBallCurrent_metric _ t)
      (hs.mono fun t ht => ht.1.neg) htest
  refine ⟨G, hG, hG0, ?_, ?_⟩
  · have hg : (∫ t : ℝ, G t) ≤ mass C.action := by simpa using hGI
    exact hg.trans (ballChart_mass_le (k+1))
  · filter_upwards [hs,heq] with t ht he
    refine ⟨⟨innerBallCurrent_metric _ t, innerBallCurrent_rectifiable _ t,
      he.symm ▸ ht.1.neg, he.symm ▸ ht.2.1.neg⟩, ?_⟩
    rw [he, mass_neg]
    exact ht.2.2

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_Calibration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open BorelCoefficients BorelRestriction MassMeasure CurrentOperations

lemma ambientCoord_lipschitz {d : ℕ} (i : Fin d) : LipschitzWith 1 (ambientCoord i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [dist_eq_norm]
  change ‖(x-y) i‖ ≤ ‖x-y‖
  exact PiLp.norm_apply_le (x-y) i

lemma unitCoord_lipschitz {d : ℕ} (i : Fin d) : LipschitzWith 1 (unitCoord i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (ambientCoord_lipschitz i).dist_le_mul x.val y.val

lemma unitCoord_bound {d : ℕ} (i : Fin d) (x : UnitBall d) : |unitCoord i x| ≤ 1 := by
  have hx : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  exact (PiLp.norm_apply_le x.val i).trans hx

lemma ballChart_jacobian_coords (d : ℕ) :
    (ballChart d).jacobian (fun i => unitCoord i) =ᵐ[volume.restrict (ballChart d).domain]
      fun _ => 1 := by
  have he (i : Fin d) : EqOn ((ballChart d).scalar (unitCoord i)) (ambientCoord i)
      (ballChart d).domain := by
    intro z hz
    rw [(ballChart d).scalar_eq hz]
    rfl
  filter_upwards [(ballChart d).ae_jacobian_eq_extensions ambientCoord_lipschitz he] with z hz
  rw [hz]
  have hM : (Matrix.of fun (i j : Fin d) =>
      fderiv ℝ (ambientCoord i) z (EuclideanSpace.single j 1)) = 1 := by
    ext i j
    change (fderiv ℝ (EuclideanSpace.proj i) z) (EuclideanSpace.single j 1) = _
    rw [ContinuousLinearMap.fderiv]
    simp [Matrix.one_apply]
  rw [hM,Matrix.det_one]

lemma innerBallCurrent_coords (d : ℕ) {t : ℝ} (ht : -1 < t) :
    innerBallCurrent d t (fun _ => 1) (fun i => unitCoord i) =
      (volume (Metric.ball (0 : Euc d) (-t))).toReal := by
  let C := ballChart d
  let E := {x : UnitBall d | t < radiusFunction d x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (radiusFunction_lipschitz d).continuous.measurable
  have had : Admissible (fun _ : UnitBall d => (1:ℝ)) (fun i => unitCoord i) :=
    ⟨BoundedLip.const 1,fun i => ⟨1,unitCoord_lipschitz i⟩⟩
  rw [innerBallCurrent, restrictCurrent_apply C.action_isMetricCurrent E had]
  rw [C.borelAction_eq_integral C.action_isMetricCurrent
    (currentMassMeasure_controls C.action_isMetricCurrent)
    (measurable_const.indicator hE) (show ∃ M : ℝ, ∀ x, |E.indicator (fun _ => (1:ℝ)) x| ≤ M from
      ⟨1,fun x => by by_cases hx : x ∈ E <;> simp [hx]⟩)
    (fun i => unitCoord i) had.2]
  calc (∫ z in C.domain, (C.multiplicity z : ℝ) * C.jacobian (fun i => unitCoord i) z *
      E.indicator (fun _ => (1:ℝ)) (C.paramExtended z)) =
      ∫ z in Metric.ball (0 : Euc d) 1,
        (Metric.ball (0 : Euc d) (-t)).indicator (fun _ => (1:ℝ)) z := by
        apply integral_congr_ae
        filter_upwards [ballChart_jacobian_coords d, ae_restrict_mem C.borel] with z hj hz
        have hp : radiusFunction d (C.paramExtended z) = -‖z‖ := by
          have hz' : z ∈ Metric.ball (0 : Euc d) 1 := hz
          simp [IntegerChart.paramExtended, hz', C, ballChart, radiusFunction]
        have he : C.paramExtended z ∈ E ↔ z ∈ Metric.ball (0 : Euc d) (-t) := by
          change t < radiusFunction d (C.paramExtended z) ↔ dist z 0 < -t
          rw [hp,dist_zero_right]
          constructor <;> intro h <;> linarith
        change (1:ℤ) * C.jacobian (fun i => unitCoord i) z * _ = _
        rw [Int.cast_one, hj, one_mul, one_mul]
        by_cases hh : z ∈ Metric.ball (0 : Euc d) (-t)
        · simp [hh,he.mpr hh]
        · simp [hh,not_congr he |>.mpr hh]
    _ = (volume (Metric.ball (0 : Euc d) (-t))).toReal := by
      rw [integral_indicator measurableSet_ball]
      simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
        Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_ball]
      rw [inter_eq_left.mpr (Metric.ball_subset_ball (show -t ≤ 1 by linarith))]

lemma omega_pos (d : ℕ) : 0 < omega d := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : Euc d) (by norm_num)).ne'
    Metric.isBounded_ball.measure_lt_top.ne

lemma ball_volume_scaling (d : ℕ) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball (0 : Euc d) r)).toReal = omega d * r^d := by
  rw [Measure.addHaar_ball_of_pos volume 0 hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, omega]
  ring

lemma abs_apply_le_mass {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) {b : X → ℝ}
    {π : Fin k → X → ℝ} (hb : BoundedLip b) (hb1 : ∀ x, |b x| ≤ 1)
    (hπ : ∀ i, LipschitzWith 1 (π i)) : |T b π| ≤ mass T := by
  apply le_csInf
  · obtain ⟨μ,hμ,hctrl⟩ := hT.finiteMass
    exact ⟨μ.real univ, μ,hμ,hctrl,rfl⟩
  · rintro r ⟨μ,hμ,hctrl,rfl⟩
    let := hμ
    apply (hctrl b π hb hπ).trans
    calc (∫ x, |b x| ∂μ) ≤ ∫ _ : X, (1:ℝ) ∂μ :=
          integral_mono ((integrable_const (1:ℝ)).mono' hb.continuous.aestronglyMeasurable
            (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb1 x)).abs
            (integrable_const 1) hb1
      _ = μ.real univ := by simp

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_BallBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality
open CurrentOperations

lemma integral_boundary {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) :
    IsIntegral k (boundarySucc T) := by
  cases k with
  | zero => exact ⟨hT.2.2.1,hT.2.2.2⟩
  | succ k =>
    refine ⟨hT.2.2.1,hT.2.2.2,?_,?_⟩
    · rw [Foundations.boundarySucc_boundarySucc hT.1]
      exact isMetricCurrent_zero _
    · rw [Foundations.boundarySucc_boundarySucc hT.1]
      exact integerRectifiable_zero _

lemma boundary_isCycle {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X (k+1)} (hT : IsMetricCurrent T) :
    IsCycle (boundarySucc T) := by
  cases k with
  | zero => rfl
  | succ k => exact Foundations.boundarySucc_boundarySucc hT

lemma push_compactlySupported {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) {f : X → Y} {L : ℝ≥0}
    (hf : LipschitzWith L f) : CompactlySupported (pushCurrent f T) := by
  refine ⟨range f, isCompact_range hf.continuous, ?_⟩
  intro b π had hb
  rw [pushCurrent_apply f T had]
  have he : b ∘ f = fun _ => 0 := funext fun x => hb (f x) ⟨x,rfl⟩
  rw [he]
  have h0 := hT.linearFirst (fun _ => 0) (fun _ => 0) (fun i => π i ∘ f) 0 0
    (BoundedLip.const 0) (BoundedLip.const 0) (admissible_comp had hf).2
  simpa only [zero_mul,add_zero] using h0

lemma clippedCoord_lipschitz {d : ℕ} (i : Fin d) : LipschitzWith 1 (clippedCoord i) :=
  ((ambientCoord_lipschitz i).const_min 1).const_max (-1)

lemma clippedCoord_abs_le {d : ℕ} (i : Fin d) (x : Euc d) : |clippedCoord i x| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

lemma clippedCoord_boundedLip {d : ℕ} (i : Fin d) : BoundedLip (clippedCoord i) :=
  ⟨⟨1,clippedCoord_lipschitz i⟩,1,clippedCoord_abs_le i⟩

lemma clippedCoord_on_unitBall {d : ℕ} (i : Fin d) (x : UnitBall d) :
    clippedCoord i x.val = unitCoord i x := by
  have hx := abs_le.mp (unitCoord_bound i x)
  change max (-1) (min 1 (unitCoord i x)) = unitCoord i x
  rw [min_eq_right hx.2,max_eq_right hx.1]

lemma inclusion_lipschitz (d : ℕ) : LipschitzWith 1 (fun x : UnitBall d => x.val) :=
  LipschitzWith.subtype_val _

lemma ambientBall_integral {d : ℕ} {t : ℝ}
    (hT : IsIntegral d (innerBallCurrent d t)) : IsIntegral d (ambientBall d t) :=
  integral_push_of_bilipschitz hT (inclusion_lipschitz d) isometry_subtype_coe.antilipschitz

lemma ambientBall_boundary_mass_le (n : ℕ) (t : ℝ)
    (hT : IsMetricCurrent (boundarySucc (innerBallCurrent (n+1) t))) :
    mass (boundarySucc (ambientBall (n+1) t)) ≤
      mass (boundarySucc (innerBallCurrent (n+1) t)) := by
  rw [ambientBall, pushCurrent_boundarySucc _ (inclusion_lipschitz (n+1))]
  simpa only [NNReal.coe_one,one_pow,one_mul] using
    mass_pushCurrent_le hT (inclusion_lipschitz (n+1))

lemma ambientBall_boundary_compact (n : ℕ) (t : ℝ)
    (hT : IsMetricCurrent (boundarySucc (innerBallCurrent (n+1) t))) :
    CompactlySupported (boundarySucc (ambientBall (n+1) t)) := by
  rw [ambientBall, pushCurrent_boundarySucc _ (inclusion_lipschitz (n+1))]
  exact push_compactlySupported hT (inclusion_lipschitz (n+1))

lemma ambientBall_boundary_coords (n : ℕ) {t : ℝ} (ht : -1 < t) :
    boundarySucc (ambientBall (n+1) t) (clippedCoord 0) (fun i => ambientCoord i.succ) =
      (volume (Metric.ball (0 : Euc (n+1)) (-t))).toReal := by
  have had : Admissible (clippedCoord (0 : Fin (n+1))) (fun i => ambientCoord i.succ) :=
    ⟨clippedCoord_boundedLip 0,fun i => ⟨1,ambientCoord_lipschitz i.succ⟩⟩
  rw [boundarySucc,ite_eq_left had,ambientBall,
    pushCurrent_apply _ _ (Foundations.admissible_vecCons (BoundedLip.const 1) had.1.1 had.2)]
  have he : (fun i => Matrix.vecCons (clippedCoord (0 : Fin (n+1)))
        (fun j => ambientCoord j.succ) i ∘ (fun x : UnitBall (n+1) => x.val)) = unitCoord := by
    funext i x
    induction i using Fin.cases with
    | zero => exact clippedCoord_on_unitBall 0 x
    | succ i => rfl
  rw [he]
  exact innerBallCurrent_coords (n+1) ht

lemma allFillings_mass_ge_ball (n : ℕ) {t : ℝ} (ht : -1 < t)
    {S : Functional (Euc (n+1)) (n+1)} (hS : IsMetricCurrent S)
    (hb : boundarySucc S = boundarySucc (ambientBall (n+1) t)) :
    (volume (Metric.ball (0 : Euc (n+1)) (-t))).toReal ≤ mass S := by
  have he := congrArg (fun U : Functional (Euc (n+1)) n =>
    U (clippedCoord 0) (fun i => ambientCoord i.succ)) hb
  rw [ambientBall_boundary_coords n ht] at he
  have had : Admissible (clippedCoord (0 : Fin (n+1))) (fun i => ambientCoord i.succ) :=
    ⟨clippedCoord_boundedLip 0,fun i => ⟨1,ambientCoord_lipschitz i.succ⟩⟩
  rw [boundarySucc,ite_eq_left had] at he
  rw [← he]
  apply (le_abs_self _).trans
  apply abs_apply_le_mass hS (BoundedLip.const 1) (fun _ => by norm_num)
  intro i
  induction i using Fin.cases with
  | zero => exact clippedCoord_lipschitz 0
  | succ i => exact ambientCoord_lipschitz i.succ

lemma ambientBall_boundary_mass_pos (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1:ℝ) 0)
    (hT : IsMetricCurrent (boundarySucc (ambientBall (n+1) t))) :
    0 < mass (boundarySucc (ambientBall (n+1) t)) := by
  have htest := abs_apply_le_mass hT (clippedCoord_boundedLip (0 : Fin (n+1)))
    (clippedCoord_abs_le 0) (fun i => ambientCoord_lipschitz i.succ)
  rw [ambientBall_boundary_coords n ht.1,abs_of_nonneg ENNReal.toReal_nonneg,
    ball_volume_scaling (n+1) (neg_pos.mpr ht.2)] at htest
  exact (mul_pos (omega_pos (n+1)) (pow_pos (neg_pos.mpr ht.2) _)).trans_le htest

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Optimality_GoodRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality

lemma exists_le_of_integral_le_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ ≠ 0) {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hi : (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ) {P : α → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ f x ≤ g x := by
  classical
  by_contra h
  push Not at h
  have hlt : ∀ᵐ x ∂μ, g x < f x := hP.mono fun x hx => h x hx
  have hnonneg : 0 ≤ᵐ[μ] fun x => f x - g x := hlt.mono fun x hx => sub_nonneg.mpr hx.le
  have hzero : (∫ x, f x - g x ∂μ) = 0 := by
    apply le_antisymm
    · rw [integral_sub hf hg]
      linarith
    · exact integral_nonneg_of_ae hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hf.sub hg)).mp hzero
  have : NeZero μ := ⟨hμ⟩
  obtain ⟨x,hx,he⟩ := (hlt.and hae).exists
  exact (sub_pos.mpr hx).ne' he

lemma integral_radial_area (n : ℕ) :
    (∫ t in Ioo (-1:ℝ) 0, ((n:ℝ)+1)*omega (n+1)*(-t)^n) = omega (n+1) := by
  let F : ℝ → ℝ := fun t => -omega (n+1)*(-t)^(n+1)
  let f : ℝ → ℝ := fun t => ((n:ℝ)+1)*omega (n+1)*(-t)^n
  have hc : Continuous f := by unfold f; fun_prop
  have hd (t : ℝ) : HasDerivAt F (f t) t := by
    have hh := (((hasDerivAt_id t).neg.pow (n+1)).const_mul (-omega (n+1)))
    convert hh using 1 <;> first | rfl | simp only [f, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.neg_apply, id_eq]; ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable (-1) 0)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hh
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  change (∫ t in Ioc (-1:ℝ) 0, f t) = _
  rw [hh]
  simp [F]

theorem exists_good_inner_ball (n : ℕ) :
    ∃ t ∈ Ioo (-1:ℝ) 0,
      IsIntegral (n+1) (innerBallCurrent (n+1) t) ∧
      mass (boundarySucc (innerBallCurrent (n+1) t)) ≤
        ((n:ℝ)+1)*omega (n+1)*(-t)^n := by
  obtain ⟨G,hG,hG0,hGI,hgood⟩ := innerBall_ae_integral n
  let μ := volume.restrict (Ioo (-1:ℝ) 0)
  let f : ℝ → ℝ := fun t => ((n:ℝ)+1)*omega (n+1)*(-t)^n
  have hμ : μ ≠ 0 := by
    intro h
    have hh := congrArg (fun m : Measure ℝ => m univ) h
    norm_num [μ] at hh
  have hf : Integrable f μ := by
    apply Continuous.integrableOn_Icc (a := (-1:ℝ)) (b := 0) (by unfold f; fun_prop) |>.mono_set
    exact Ioo_subset_Icc_self
  have hi : (∫ t, G t ∂μ) ≤ ∫ t, f t ∂μ := by
    calc (∫ t, G t ∂μ) ≤ ∫ t, G t :=
        setIntegral_le_integral hG (Eventually.of_forall hG0)
      _ ≤ omega (n+1) := hGI
      _ = ∫ t, f t ∂μ := (integral_radial_area n).symm
  obtain ⟨t,⟨ht,htI,htM⟩,hle⟩ := exists_le_of_integral_le_ae hμ hG.restrict hf hi
    ((ae_restrict_mem measurableSet_Ioo).and hgood)
  exact ⟨t,ht,htI,htM.trans hle⟩

end SharpIntegralFillings.Optimality

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
namespace Optimality

lemma sphereArea_pos (n : ℕ) : 0 < sphereArea n :=
  mul_pos (by positivity) (omega_pos (n+1))

lemma fillingCoefficient_pos (n : ℕ) : 0 < fillingCoefficient n := by
  unfold fillingCoefficient
  exact one_div_pos.mpr (mul_pos (by positivity) (Real.rpow_pos_of_pos (sphereArea_pos n) _))

lemma sharp_ball_identity {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    fillingCoefficient n * (sphereArea n * r^n) ^ fillingPower n = omega (n+1)*r^(n+1) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : fillingPower n = 1 + 1/(n:ℝ) := by unfold fillingPower; field_simp
  have hnp : (n:ℝ)*fillingPower n = ((n+1:ℕ):ℝ) := by
    unfold fillingPower
    push_cast
    field_simp
  rw [Real.mul_rpow (sphereArea_pos n).le (pow_nonneg hr _),
    ← Real.rpow_natCast_mul hr, hnp, Real.rpow_natCast]
  rw [hp, Real.rpow_add (sphereArea_pos n),Real.rpow_one]
  unfold fillingCoefficient
  have hroot : (sphereArea n)^(1/(n:ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (sphereArea_pos n) _).ne'
  have hdn : (n:ℝ)+1 ≠ 0 := by positivity
  calc 1 / (((n:ℝ)+1) * (sphereArea n)^(1/(n:ℝ))) *
        (sphereArea n * (sphereArea n)^(1/(n:ℝ)) * r^(n+1)) =
       (sphereArea n / ((n:ℝ)+1))*r^(n+1) := by field_simp
    _ = omega (n+1)*r^(n+1) := by unfold sphereArea; field_simp

lemma sharp_ball_bound {n : ℕ} (hn : 0 < n) {r m : ℝ} (hr : 0 < r)
    (hm : 0 ≤ m) (hmle : m ≤ sphereArea n*r^n) :
    fillingCoefficient n * m^fillingPower n ≤ omega (n+1)*r^(n+1) := by
  rw [← sharp_ball_identity hn hr.le]
  apply mul_le_mul_of_nonneg_left _ (fillingCoefficient_pos n).le
  apply Real.rpow_le_rpow hm hmle
  unfold fillingPower
  positivity

end Optimality

theorem coefficient_optimal_oai (n : ℕ) (hn : 2 ≤ n) :
    ∃ T : IntegralCurrent (Euc (n + 1)) n,
      CompactlySupported T.val ∧ IsCycle T.val ∧ 0 < mass T.val ∧
      ∀ S : IntegralCurrent (Euc (n + 1)) (n + 1),
        CompactlySupported S.val → boundarySucc S.val = T.val →
        fillingCoefficient n * (mass T.val) ^ fillingPower n ≤ mass S.val := by
  obtain ⟨t,ht,hI,hM⟩ := Optimality.exists_good_inner_ball n
  have hAI := Optimality.ambientBall_integral hI
  let B := Optimality.ambientBall (n+1) t
  let T : IntegralCurrent (Euc (n+1)) n := ⟨boundarySucc B,Optimality.integral_boundary hAI⟩
  refine ⟨T,Optimality.ambientBall_boundary_compact n t hI.2.2.1,
    Optimality.boundary_isCycle hAI.1, Optimality.ambientBall_boundary_mass_pos n ht hAI.2.2.1, ?_⟩
  intro S hSc hSb
  have hmass : mass T.val ≤ sphereArea n * (-t)^n :=
    (Optimality.ambientBall_boundary_mass_le n t hI.2.2.1).trans hM
  calc fillingCoefficient n * mass T.val ^ fillingPower n ≤ omega (n+1)*(-t)^(n+1) :=
      Optimality.sharp_ball_bound (by omega) (neg_pos.mpr ht.2) (mass_nonneg _) hmass
    _ = (volume (Metric.ball (0 : Euc (n+1)) (-t))).toReal :=
      (Optimality.ball_volume_scaling (n+1) (neg_pos.mpr ht.2)).symm
    _ ≤ mass S.val := Optimality.allFillings_mass_ge_ball n ht.1 S.property.1 hSb

end SharpIntegralFillings

end

end OAI
end

theorem solution : type_of% @OAI.SharpIntegralFillings.coefficient_optimal_oai := @OAI.SharpIntegralFillings.coefficient_optimal_oai
