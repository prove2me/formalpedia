-- Prove2me | solution 1 for OAI.SharpIntegralFillings.IntegerChart.hilbert_mass_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:34:24.238622+00:00
-- url     : https://prove2.me/submissions/c5a17ed2-f1fc-4145-b0fd-4e6f62f70d81

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000

section
-- module Solutions.OAIQ219_IF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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

lemma dot_mulVec_sqrt {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    v ⬝ᵥ P.mulVec v = (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v := by
  have hsym : (CFC.sqrt P).transpose = CFC.sqrt P :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P).posSemidef.isHermitian).eq
  conv_lhs => rw [← CFC.sq_sqrt P hP.nonneg,pow_two, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]

lemma row_norm_le_of_dot_bound_const {n : ℕ} (a : Fin n → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ, |a ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ K := by
  have hh := h a
  have heq : a ⬝ᵥ a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, star_trivial] using
      real_inner_self_eq_norm_sq (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))
  rw [heq,abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))]

lemma abs_det_le_pow_of_dot_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ i v, |A i ⬝ᵥ v| ≤ K*‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) :
    |A.det| ≤ K^n := by
  apply (abs_det_le_prod_row_norm A).trans
  calc
    _ ≤ ∏ _i : Fin n, K := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => row_norm_le_of_dot_bound_const _ hK (h i))
    _ = K^n := by simp

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_MatrixRows
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
open Matrix
open scoped RealInnerProductSpace MatrixOrder

lemma norm_sqrt_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (v : Fin n → ℝ) :
    ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (v ⬝ᵥ P.mulVec v) := by
  rw [dot_mulVec_sqrt P hP]
  have heq : (CFC.sqrt P).mulVec v ⬝ᵥ (CFC.sqrt P).mulVec v =
      ‖(WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))‖^2 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,WithLp.ofLp_toLp,star_trivial] using
      real_inner_self_eq_norm_sq
        (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n))
  rw [heq,Real.sqrt_sq (norm_nonneg _)]

lemma sqrt_det_le_mul_sqrt_det {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosDef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : Fin n → ℝ,
      Real.sqrt (v ⬝ᵥ P.mulVec v) ≤ K*Real.sqrt (v ⬝ᵥ Q.mulVec v)) :
    Real.sqrt P.det ≤ K^n * Real.sqrt Q.det := by
  let A := CFC.sqrt P
  let B := CFC.sqrt Q
  have hAdet : A.det = Real.sqrt P.det := by
    simpa only [RCLike.sqrt_real] using hP.det_sqrt
  have hBdet : B.det = Real.sqrt Q.det := by
    simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt
  have hBp : 0 < B.det := by rw [hBdet]; exact Real.sqrt_pos.2 hQ.det_pos
  have hBi : IsUnit B.det := isUnit_iff_ne_zero.2 (ne_of_gt hBp)
  have hBinv := Matrix.mul_nonsing_inv B hBi
  have hinvB := Matrix.nonsing_inv_mul B hBi
  have htrans (v : Fin n → ℝ) :
      Real.sqrt ((B⁻¹).mulVec v ⬝ᵥ Q.mulVec ((B⁻¹).mulVec v)) =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
    rw [←norm_sqrt_mulVec Q hQ.posSemidef]
    change ‖(WithLp.toLp 2 (B.mulVec ((B⁻¹).mulVec v)) : EuclideanSpace ℝ (Fin n))‖ = _
    rw [Matrix.mulVec_mulVec,hBinv,Matrix.one_mulVec]
  have hbound : |(A * B⁻¹).det| ≤ K^n := by
    apply abs_det_le_pow_of_dot_bound _ hK
    intro i v
    have hh := h ((B⁻¹).mulVec v)
    rw [htrans,←norm_sqrt_mulVec P hP] at hh
    apply le_trans _ hh
    have hv : (A * B⁻¹) i ⬝ᵥ v = (A.mulVec ((B⁻¹).mulVec v)) i := by
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [hv]
    exact PiLp.norm_apply_le
      (WithLp.toLp 2 (A.mulVec ((B⁻¹).mulVec v)) : EuclideanSpace ℝ (Fin n)) i
  have heq : A = (A*B⁻¹)*B := by rw [Matrix.mul_assoc,hinvB,Matrix.mul_one]
  calc
    Real.sqrt P.det = |A.det| := by rw [hAdet,abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = |(A*B⁻¹).det| *B.det := by
      conv_lhs => rw [heq,Matrix.det_mul]
      rw [abs_mul,abs_of_pos hBp]
    _ ≤ K^n*B.det := mul_le_mul_of_nonneg_right hbound hBp.le
    _ = K^n*Real.sqrt Q.det := by rw [hBdet]

lemma abs_matrixRow_sqrt_le {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    |matrixRowFunctional (CFC.sqrt P) i v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v) := by
  rw [matrixRowFunctional_apply,←norm_sqrt_mulVec P hP]
  exact PiLp.norm_apply_le
    (WithLp.toLp 2 ((CFC.sqrt P).mulVec v) : EuclideanSpace ℝ (Fin n)) i

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Polarization
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

namespace SharpIntegralFillings
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma exists_bilinForm_of_parallelogram (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ B : LinearMap.BilinForm ℝ E, B.IsSymm ∧ B.toQuadraticMap.PosDef ∧
      (∀ v, B v v = (p v)^2) ∧
      ∀ u v, B u v = ((p (u+v))^2-(p (u-v))^2)/4 := by
  let : Norm E := ⟨p⟩
  let core : NormedSpace.Core ℝ E :=
    { norm_nonneg := fun v => apply_nonneg p v
      norm_smul := fun c v => map_smul_eq_mul p c v
      norm_triangle := fun x y => map_add_le_add p x y
      norm_eq_zero_iff := hp }
  let : NormedAddCommGroup E := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ E := NormedSpace.ofCore core
  have hparanorm : ∀ u v : E,
      ‖u+v‖*‖u+v‖+‖u-v‖*‖u-v‖ = 2*(‖u‖*‖u‖+‖v‖*‖v‖) := by
    intro u v
    change p (u+v)*p (u+v)+p (u-v)*p (u-v) = 2*(p u*p u+p v*p v)
    nlinarith [hpara u v]
  let : InnerProductSpace ℝ E := InnerProductSpace.ofNorm ℝ hparanorm
  refine ⟨innerₗ E,?_,?_,?_,?_⟩
  · exact ⟨fun u v => (real_inner_comm u v).symm⟩
  · intro v hv
    change 0 < inner ℝ v v
    exact real_inner_self_pos.mpr hv
  · intro v
    change inner ℝ v v = (p v)^2
    exact real_inner_self_eq_norm_sq v
  · intro u v
    change inner ℝ u v = ((p (u+v))^2-(p (u-v))^2)/4
    have H := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) u v
    change inner ℝ u v = (p (u+v)*p (u+v)-p (u-v)*p (u-v))/4 at H
    simpa only [pow_two] using H

lemma polarizationMatrix_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    (polarizationMatrix p b).PosDef := by
  obtain ⟨B,hB,hpos,_,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b B hB).1 hpos

lemma polarizationMatrix_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (p : Seminorm ℝ E)
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : E) :
    (b.repr v) ⬝ᵥ (polarizationMatrix p b).mulVec (b.repr v) = (p v)^2 := by
  obtain ⟨B,_,_,hdiag,hpol⟩ := exists_bilinForm_of_parallelogram p hp hpara
  have heq : polarizationMatrix p b = B.toMatrix b := by
    ext i j
    simpa only [polarizationMatrix, LinearMap.BilinForm.toMatrix_apply] using (hpol (b i) (b j)).symm
  rw [heq]
  rw [←hdiag v]
  exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B v v).symm

end SharpIntegralFillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_MeasurePartition
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

lemma densityPush_mono_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {φ : α → β} (hφ : Measurable φ) {ρ σ : α → ℝ}
    (h : ρ ≤ᵐ[μ] σ) : densityPush μ φ ρ ≤ densityPush μ φ σ := by
  rw [densityPush_eq_map μ hφ, densityPush_eq_map μ hφ]
  apply Measure.map_mono _ hφ
  exact withDensity_mono (h.mono fun _ hx => ENNReal.ofReal_le_ofReal hx)

lemma densityPush_const_mul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (φ : α → β) (ρ : α → ℝ) (c : ℝ≥0) :
    densityPush μ φ (fun z => (c : ℝ)*ρ z) = c • densityPush μ φ ρ := by
  by_cases hc : c = 0
  · subst c
    simp [densityPush]
  unfold densityPush
  have hfun : (fun z => ENNReal.ofReal ((c : ℝ)*ρ z)) =
      (c : ENNReal) • (fun z => ENNReal.ofReal (ρ z)) := by
    ext z
    simp only [Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_mul c.coe_nonneg,ENNReal.ofReal_coe_nnreal]
  rw [hfun,withDensity_smul' _ _ ENNReal.coe_ne_top,
    aemeasurable_smul_measure_iff (ENNReal.coe_ne_zero.mpr hc)]
  by_cases hφ : AEMeasurable φ (μ.withDensity fun z => ENNReal.ofReal (ρ z))
  · simp only [ite_eq_left hφ]
    rw [Measure.map_smul]
    rfl
  · simp only [ite_eq_right hφ, smul_zero]

lemma densityPush_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ι : Type*} (μ : ι → Measure α) {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ) :
    densityPush (Measure.sum μ) φ ρ = Measure.sum (fun i => densityPush (μ i) φ ρ) := by
  simp only [densityPush_eq_map _ hφ,withDensity_sum,Measure.map_sum hφ.aemeasurable]

lemma restrict_eq_sum_of_ae_partition {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} {t : ℕ → Set α}
    (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (t i) (t j))) (hnull : μ (s \ ⋃ i, t i) = 0) :
    μ.restrict s = Measure.sum (fun i => μ.restrict (t i)) := by
  have hsub : (⋃ i, t i) ⊆ s := iUnion_subset hts
  have heq : s =ᵐ[μ] ⋃ i, t i := ae_eq_set.mpr ⟨hnull,by simp only [sdiff_eq_empty.mpr hsub,measure_empty]⟩
  rw [Measure.restrict_congr_set heq,Measure.restrict_iUnion hdisj ht]

lemma densityPush_le_of_partition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {φ : α → β} (hφ : Measurable φ) (ρ : α → ℝ)
    {s : Set α} {t : ℕ → Set α} (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (fun i j => Disjoint (t i) (t j))) (hnull : μ (s \ ⋃ i, t i) = 0)
    (him : ∀ i, MeasurableSet (φ '' t i)) (hinj : Set.InjOn φ s)
    (hbound : ∀ i, densityPush (μ.restrict (t i)) φ ρ ≤ ν.restrict (φ '' t i)) :
    densityPush (μ.restrict s) φ ρ ≤ ν := by
  rw [restrict_eq_sum_of_ae_partition ht hts hdisj hnull,densityPush_sum _ hφ]
  have hdisj' : Pairwise (fun i j => Disjoint (φ '' t i) (φ '' t j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hxi,rfl⟩ ⟨y,hyj,hxy⟩
    have hxy' : y = x := hinj (hts j hyj) (hts i hxi) hxy
    subst y
    exact Set.disjoint_left.mp (hdisj hij) hxi hyj
  calc
    _ ≤ Measure.sum (fun i => ν.restrict (φ '' t i)) := by
      apply Measure.le_iff.mpr
      intro u hu
      simp only [Measure.sum_apply _ hu]
      exact ENNReal.tsum_le_tsum (fun i => hbound i u)
    _ = ν.restrict (⋃ i, φ '' t i) := (Measure.restrict_iUnion hdisj' him).symm
    _ ≤ ν := Measure.restrict_le_self
end SharpIntegralFillings

namespace SharpIntegralFillings
open Matrix MeasureTheory Set Filter
open scoped MatrixOrder NNReal Topology

lemma sqrt_polarization_quadratic {k : ℕ} (p : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) (v : Fin k → ℝ) :
    Real.sqrt (v ⬝ᵥ (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).mulVec v)
      = p (WithLp.toLp 2 v) := by
  have hrepr : (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.repr (WithLp.toLp 2 v) = v := by
    ext j
    simp
  have hquad := polarizationMatrix_quadratic (EuclideanSpace.basisFun (Fin k) ℝ).toBasis p hp hpara (WithLp.toLp 2 v)
  rw [hrepr] at hquad
  rw [hquad,Real.sqrt_sq (apply_nonneg _ _)]

lemma sqrt_det_polarization_le {k : ℕ} (p q : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0) (hq : ∀ v, q v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    (hqpara : ∀ u v, q (u+v)^2+q (u-v)^2 = 2*q u^2+2*q v^2)
    {L : ℝ} (hL : 0 ≤ L) (h : ∀ v, p v ≤ L*q v) :
    Real.sqrt (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≤
    L^k * Real.sqrt (polarizationMatrix q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  apply sqrt_det_le_mul_sqrt_det _ _
    (polarizationMatrix_posDef _ p hp hpara).posSemidef
    (polarizationMatrix_posDef _ q hq hqpara) hL
  intro v
  simpa only [sqrt_polarization_quadratic p hp hpara,
    sqrt_polarization_quadratic q hq hqpara] using h (WithLp.toLp 2 v)

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_CurveSpeed
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiationDense
variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X] {f : ℝ → X} {K : ℝ≥0}

lemma coordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (distanceCoordinate f q) := by
  change LipschitzWith K (fun t : ℝ => dist (f t) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma coordinate_deriv_bound (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ K := by
  simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (coordinate_lipschitz hf q)

lemma coordinate_deriv_le_speed (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ metricSpeed f t :=
  le_ciSup ⟨(K : ℝ), by rintro v ⟨r, rfl⟩; exact coordinate_deriv_bound hf r t⟩ q

lemma metricSpeed_nonneg (hf : LipschitzWith K f) (t : ℝ) : 0 ≤ metricSpeed f t :=
  (abs_nonneg _).trans (coordinate_deriv_le_speed hf 0 t)

lemma metricSpeed_le (hf : LipschitzWith K f) (t : ℝ) : metricSpeed f t ≤ K :=
  ciSup_le (fun q => coordinate_deriv_bound hf q t)

lemma measurable_metricSpeed (f : ℝ → X) : Measurable (metricSpeed f) :=
  Measurable.iSup (fun q => (measurable_deriv (distanceCoordinate f q)).abs)

lemma locallyIntegrable_metricSpeed (hf : LipschitzWith K f) :
    LocallyIntegrable (metricSpeed f) volume := by
  apply (memLp_top_of_bound (measurable_metricSpeed f).aestronglyMeasurable (K : ℝ) ?_).locallyIntegrable le_top
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (metricSpeed_nonneg hf t)]
    exact metricSpeed_le hf t

lemma intervalIntegrable_metricSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    IntervalIntegrable (metricSpeed f) volume s t :=
  intervalIntegrable_iff.mpr
    (((locallyIntegrable_metricSpeed hf).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

lemma coordinate_difference_bound (hf : LipschitzWith K f) (q : ℕ) {s t : ℝ} (hst : s ≤ t) :
    |distanceCoordinate f q t - distanceCoordinate f q s| ≤ ∫ x in s..t, metricSpeed f x := by
  have hac := (coordinate_lipschitz hf q).lipschitzOnWith.absolutelyContinuousOnInterval (a := s) (b := t)
  rw [← hac.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm hst).trans
  apply intervalIntegral.integral_mono_on hst hac.intervalIntegrable_deriv.norm
    (intervalIntegrable_metricSpeed hf s t)
  intro x hx
  exact coordinate_deriv_le_speed hf q x

lemma distance_le_integral_speed (hf : LipschitzWith K f) {s t : ℝ} (hst : s ≤ t) :
    dist (f t) (f s) ≤ ∫ x in s..t, metricSpeed f x := by
  have hc : Continuous (fun y : X => |dist (f t) y - dist (f s) y|) :=
    ((continuous_const.dist continuous_id).sub (continuous_const.dist continuous_id)).abs
  have h := (denseRange_denseSeq X).induction_on
    (p := fun y : X => |dist (f t) y - dist (f s) y| ≤
      ∫ x in s..t, metricSpeed f x) (f s) (isClosed_le hc continuous_const)
      (fun q => coordinate_difference_bound hf q hst)
  simpa using h

lemma distance_le_integratedSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    dist (f t) (f s) ≤ |integratedSpeed f t - integratedSpeed f s| := by
  have hi (a b : ℝ) := intervalIntegrable_metricSpeed hf a b
  have hd (a b : ℝ) : integratedSpeed f b - integratedSpeed f a =
      ∫ x in a..b, metricSpeed f x := by
    exact intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  rcases le_total s t with hst | hts
  · rw [hd s t, abs_of_nonneg (intervalIntegral.integral_nonneg hst
      (fun x hx => metricSpeed_nonneg hf x))]
    exact distance_le_integral_speed hf hst
  · rw [abs_sub_comm, hd t s, abs_of_nonneg (intervalIntegral.integral_nonneg hts
      (fun x hx => metricSpeed_nonneg hf x)), dist_comm]
    exact distance_le_integral_speed hf hts

lemma abs_slope_tendsto {g : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt g d x) :
    Tendsto (fun t => |g t-g x|/|t-x|) (𝓝[≠] x) (𝓝 |d|) := by
  simpa only [slope, norm_smul, norm_inv, Real.norm_eq_abs, vsub_eq_sub, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope.norm

theorem ae_hasMetricDerivAt (hf : LipschitzWith K f) :
    ∀ᵐ x, HasMetricDerivAt f (metricSpeed f x) x := by
  have hcoords : ∀ᵐ x, ∀ q : ℕ, DifferentiableAt ℝ (distanceCoordinate f q) x := by
    rw [ae_all_iff]
    intro q
    exact (coordinate_lipschitz hf q).ae_differentiableAt_real
  have hint := LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_metricSpeed hf)
  filter_upwards [hcoords, hint] with x hx hI
  have hg := abs_slope_tendsto (hI 0)
  rw [abs_of_nonneg (metricSpeed_nonneg hf x)] at hg
  change Tendsto (fun t => |integratedSpeed f t-integratedSpeed f x|/|t-x|)
    (𝓝[≠] x) (𝓝 (metricSpeed f x)) at hg
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hb : BddAbove (range (fun q : ℕ => |deriv (distanceCoordinate f q) x|)) :=
      ⟨(K : ℝ), by rintro v ⟨q, rfl⟩; exact coordinate_deriv_bound hf q x⟩
    obtain ⟨q, hq⟩ := (lt_ciSup_iff hb).mp hc
    have hd := abs_slope_tendsto (hx q).hasDerivAt
    filter_upwards [hd.eventually (eventually_gt_nhds hq)] with t ht
    exact ht.trans_le (div_le_div_of_nonneg_right
      (abs_dist_sub_le (f t) (f x) (denseSeq X q)) (abs_nonneg _))
  · intro c hc
    filter_upwards [hg.eventually (eventually_lt_nhds hc)] with t ht
    exact (div_le_div_of_nonneg_right (distance_le_integratedSpeed hf x t) (abs_nonneg _)).trans_lt ht

end SharpIntegralFillings.MetricDifferentiationDense

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Directional
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
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {X : Type*} [MetricSpace X]

lemma signedDistance_zero (c : ℝ → X) : signedDistance c 0 = 0 := by
  simp [signedDistance]

lemma signedDistance_div (c : ℝ → X) (t : ℝ) :
    signedDistance c t / t = dist (c t) (c 0) / |t| := by
  rcases le_total 0 t with ht | ht
  · simp [signedDistance, ht, abs_of_nonneg ht]
  · by_cases h0 : t = 0
    · simp [h0]
    · simp [signedDistance, not_le.mpr (lt_of_le_of_ne ht h0), abs_of_nonpos ht, neg_div, div_neg]

lemma hasDerivAt_signedDistance_iff (c : ℝ → X) (d : ℝ) :
    HasDerivAt (signedDistance c) d 0 ↔
      Tendsto (fun t => dist (c t) (c 0) / |t|) (𝓝[≠] 0) (𝓝 d) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, signedDistance_zero, sub_zero, smul_eq_mul, ← div_eq_inv_mul,
    signedDistance_div]

lemma continuous_signedDistance {A : Type*} [TopologicalSpace A] {c : A → ℝ → X}
    (hc : Continuous c.uncurry) : Continuous (fun p : A × ℝ => signedDistance (c p.1) p.2) := by
  have hd : Continuous (fun p : A × ℝ => dist (c p.1 p.2) (c p.1 0)) :=
    hc.dist (hc.comp (continuous_fst.prodMk continuous_const))
  exact hd.if_le hd.neg continuous_const continuous_snd (by
    rintro ⟨x,t⟩ (h : 0 = t)
    simp [← h])

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
lemma scalarCoordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (scalarCoordinate f q) := by
  change LipschitzWith K (fun x : E => dist (f x) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using
    (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma measurable_lineSpeed (hf : Continuous f) (v : E) : Measurable (lineSpeed f v) := by
  apply Measurable.iSup
  intro q
  exact (measurable_lineDeriv (hf.dist continuous_const)).abs

omit [MeasurableSpace E] [BorelSpace E] in
lemma deriv_coordinate_line (p v : E) (s : ℝ) (q : ℕ) :
    deriv (MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q) s =
      lineDeriv ℝ (scalarCoordinate f q) (p+s • v) v := by
  rw [lineDeriv]
  have he : (fun t : ℝ => scalarCoordinate f q (p+s • v+t • v)) =
      (fun t : ℝ => MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q (s+t)) := by
    ext t
    simp [scalarCoordinate, MetricDifferentiationDense.distanceCoordinate, add_smul, add_assoc]
  rw [he]
  simpa using (deriv_comp_const_add (f := MetricDifferentiationDense.distanceCoordinate
    (fun t => f (p+t • v)) q) s 0).symm

omit [MeasurableSpace E] [BorelSpace E] in
lemma lineSpeed_eq_curveSpeed (p v : E) (s : ℝ) :
    lineSpeed f v (p+s • v) = MetricDifferentiationDense.metricSpeed (fun t => f (p+t • v)) s := by
  simp only [lineSpeed, MetricDifferentiationDense.metricSpeed, deriv_coordinate_line]

lemma measurableSet_hasMetricDirectionalDeriv (hf : Continuous f) (v : E) :
    MeasurableSet {x | Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x))} := by
  let c : E → ℝ → X := fun x t => f (x + t • v)
  have hc : Continuous c.uncurry := hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hD := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => signedDistance (c x) t) (continuous_signedDistance hc)
  have hder := measurable_deriv_with_param (f := fun x t => signedDistance (c x) t)
    (continuous_signedDistance hc)
  have hm := (measurable_prodMk_right (y := (0 : ℝ)) hD).inter
    (measurableSet_eq_fun (hder.comp (measurable_prodMk_right (y := (0 : ℝ)))) (measurable_lineSpeed hf v))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro ht
    have hd := (hasDerivAt_signedDistance_iff (c x) (lineSpeed f v x)).mpr (by simpa [c] using ht)
    exact ⟨hd.differentiableAt, hd.deriv⟩
  · rintro ⟨hd, he⟩
    rw [← he]
    simpa [c] using (hasDerivAt_signedDistance_iff (c x) _).mp hd.hasDerivAt

lemma tendsto_add_zero_punctured (s : ℝ) :
    Tendsto (fun t : ℝ => s+t) (𝓝[≠] 0) (𝓝[≠] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => s) (𝓝 0) (𝓝 s)).add tendsto_id).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

theorem ae_hasMetricDirectionalDeriv [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x)) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  apply ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
    (measurableSet_hasMetricDirectionalDeriv hf.continuous v)
  intro p
  have hcurve := hf.comp ((LipschitzWith.const p).add L.lipschitz)
  filter_upwards [MetricDifferentiationDense.ae_hasMetricDerivAt hcurve] with s hs
  change Tendsto (fun t : ℝ => dist (f (p+s • v+t • v)) (f (p+s • v)) / |t|)
    (𝓝[≠] 0) (𝓝 (lineSpeed f v (p+s • v)))
  rw [lineSpeed_eq_curveSpeed]
  have hh := hs.comp (tendsto_add_zero_punctured s)
  simpa only [Function.comp_def, L, MetricDifferentiationDense.HasMetricDerivAt,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    add_smul, add_assoc, add_sub_cancel_left] using hh

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Seminorm
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma coordinateSeminorm_le (hf : LipschitzWith K f) (x : E) (q : ℕ) :
    coordinateSeminorm f x q ≤ K • normSeminorm ℝ E := by
  intro v
  change ‖fderiv ℝ (scalarCoordinate f q) x v‖ ≤ (K : ℝ) * ‖v‖
  exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ (scalarCoordinate_lipschitz hf q)) (norm_nonneg _))

lemma bddAbove_coordinateSeminorm (hf : LipschitzWith K f) (x : E) :
    BddAbove (range (coordinateSeminorm f x)) :=
  ⟨K • normSeminorm ℝ E, by rintro p ⟨q,rfl⟩; exact coordinateSeminorm_le hf x q⟩

lemma metricSeminorm_apply (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v = ⨆ q : ℕ, |fderiv ℝ (scalarCoordinate f q) x v| := by
  rw [metricSeminorm, Seminorm.iSup_apply (bddAbove_coordinateSeminorm hf x)]
  rfl

lemma metricSeminorm_le (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v ≤ (K : ℝ) * ‖v‖ :=
  (ciSup_le (fun q => coordinateSeminorm_le hf x q) :
    metricSeminorm f x ≤ K • normSeminorm ℝ E) v

lemma metricSeminorm_lipschitz (hf : LipschitzWith K f) (x : E) :
    LipschitzWith K (metricSeminorm f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
  exact ((metricSeminorm f x).norm_sub_map_le_sub v w).trans (metricSeminorm_le hf x (v-w))

lemma lineSpeed_eq_metricSeminorm (hf : LipschitzWith K f) {x : E}
    (hx : ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x) (v : E) :
    lineSpeed f v x = metricSeminorm f x v := by
  rw [metricSeminorm_apply hf]
  simp only [lineSpeed, (hx _).lineDeriv_eq_fderiv]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ae_dense_directionalSeminorm (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (metricSeminorm f x (denseSeq E j))) := by
  have hcoord : ∀ᵐ x ∂μ, ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x := by
    rw [ae_all_iff]
    exact fun q => (scalarCoordinate_lipschitz hf q).ae_differentiableAt
  have hdir : ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (lineSpeed f (denseSeq E j) x)) := by
    rw [ae_all_iff]
    exact fun j => ae_hasMetricDirectionalDeriv μ hf _
  filter_upwards [hcoord, hdir] with x hx hd j
  simpa only [lineSpeed_eq_metricSeminorm hf hx] using hd j

end SharpIntegralFillings.MetricDifferentiation

open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric

lemma uniformly_tendsto_of_lipschitz {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {s : Set A} (hs : IsCompact s)
    (hlim : ∀ x ∈ s, Tendsto (fun j => f j x) l (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ x ∈ s, dist (f j x) (g x) < ε := by
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, hts, ht, hcov⟩ := hs.finite_cover_balls hδ
  have hev : ∀ᶠ j in l, ∀ y ∈ t, dist (f j y) (g y) < ε/2 := by
    rw [ht.eventually_all]
    exact fun y hy => (Metric.tendsto_nhds.mp (hlim y (hts hy))) (ε/2) (half_pos hε)
  filter_upwards [hev] with j hj x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, dist x y < δ := by
    rcases mem_iUnion.mp (hcov hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hball⟩
    exact ⟨y, hyt, hball⟩
  have hdr : (K : ℝ) * dist x y < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hxy (show 0 < (K : ℝ)+1 by positivity)
    have heq : ((K : ℝ)+1)*δ = ε/4 := by dsimp [δ]; field_simp
    rw [heq] at hm
    exact lt_of_le_of_lt (by nlinarith [dist_nonneg (x := x) (y := y)]) hm
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j y) + dist (f j y) (g y) + dist (g y) (g x) :=
        (dist_triangle _ (g y) _).trans (add_le_add (dist_triangle _ (f j y) _) le_rfl)
    _ < ε/4 + ε/2 + ε/4 := by
      apply add_lt_add
      · exact add_lt_add (((hf j).dist_le_mul x y).trans_lt hdr) (hj y hy)
      · rw [dist_comm]
        exact (hg.dist_le_mul x y).trans_lt hdr
    _ = ε := by ring
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Centered
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}

lemma metricQuotient_lipschitz (hf : LipschitzWith K f) (x : E) (t : ℝ) :
    LipschitzWith K (metricQuotient f x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  by_cases ht : t = 0
  · simp only [metricQuotient, ht, abs_zero, div_zero, dist_self]
    positivity
  have ht' : 0 < |t| := abs_pos.mpr ht
  simp only [metricQuotient, Real.dist_eq, ← sub_div, abs_div, abs_abs]
  calc |dist (f (x+t • v)) (f x) - dist (f (x+t • w)) (f x)|/|t| ≤
        dist (f (x+t • v)) (f (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (abs_dist_sub_le _ _ _) ht'.le
    _ ≤ ((K : ℝ) * dist (x+t • v) (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (hf.dist_le_mul _ _) ht'.le
    _ = (K : ℝ) * dist v w := by
      rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, dist_eq_norm]
      field_simp

lemma hasCenteredMetricDifferential_of_dense_directions [FiniteDimensional ℝ E]
    (hf : LipschitzWith K f) (x : E) (p : Seminorm ℝ E)
    (hp : LipschitzWith K p) {ι : Type*} {D : ι → E} (hD : DenseRange D)
    (hdir : ∀ j, Tendsto (fun t => metricQuotient f x t (D j)) (𝓝[≠] 0) (𝓝 (p (D j)))) :
    HasCenteredMetricDifferential f p x := by
  have hall (v : E) : Tendsto (fun t => metricQuotient f x t v) (𝓝[≠] 0) (𝓝 (p v)) :=
    tendsto_of_lipschitz_dense (metricQuotient_lipschitz hf x) hp hD hdir v
  apply IsLittleO.of_bound
  intro ε hε
  have hU := uniformly_tendsto_of_lipschitz (metricQuotient_lipschitz hf x) hp
    (isCompact_sphere (0 : E) 1) (fun v _ => hall v) hε
  obtain ⟨δ, hδ, hUδ⟩ := Metric.mem_nhdsWithin_iff.mp hU
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  let r : ℝ := ‖y-x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let v : E := r⁻¹ • (y-x)
  have hv : v ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hrv : r • v = y-x := by dsimp [v]; exact smul_inv_smul₀ hr.ne' _
  have hry : x+r • v = y := by rw [hrv]; abel
  have hrδ : r ∈ ball (0 : ℝ) δ ∩ ({0} : Set ℝ)ᶜ := by
    constructor
    · change |r-0| < δ
      rw [sub_zero, abs_of_pos hr]
      simpa only [mem_ball, dist_eq_norm, r] using hy
    · exact hr.ne'
  have hh := hUδ hrδ v hv
  change dist (dist (f (x+r • v)) (f x)/|r|) (p v) < ε at hh
  rw [hry, abs_of_pos hr, Real.dist_eq] at hh
  have hpv : p (y-x) = r * p v := by
    rw [← hrv, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hpv, Real.norm_eq_abs]
  change |dist (f y) (f x)-r*p v| ≤ ε*r
  have heq : dist (f y) (f x)-r*p v = r*(dist (f y) (f x)/r-p v) := by field_simp
  rw [heq, abs_mul, abs_of_pos hr]
  exact (mul_lt_mul_of_pos_left hh hr).le.trans_eq (mul_comm r ε)

variable [SeparableSpace X] [Nonempty X] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

theorem ae_hasCenteredMetricDifferential (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, HasCenteredMetricDifferential f (metricSeminorm f x) x := by
  filter_upwards [ae_dense_directionalSeminorm μ hf] with x hx
  exact hasCenteredMetricDifferential_of_dense_directions hf x _ (metricSeminorm_lipschitz hf x)
    (denseRange_denseSeq E) hx

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ErrorModulus
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
omit [FiniteDimensional ℝ E] in
lemma measurable_metricSeminorm_apply (hf : LipschitzWith K f) (v : E) :
    Measurable (fun x => metricSeminorm f x v) := by
  simp only [metricSeminorm_apply hf]
  exact Measurable.iSup (fun q => (measurable_fderiv_apply_const ℝ (scalarCoordinate f q) v).abs)

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_nonneg (r : ℝ) (q : ℕ) (x : E) :
    0 ≤ metricErrorTerm f r q x := by
  dsimp [metricErrorTerm]
  split_ifs
  · positivity
  · rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_le (hf : LipschitzWith K f) (r : ℝ) (q : ℕ) (x : E) :
    metricErrorTerm f r q x ≤ 2*(K : ℝ) := by
  dsimp [metricErrorTerm]
  split_ifs with h
  · apply (div_le_iff₀ h.1).mpr
    have hd : dist (f (x+denseSeq E q)) (f x) ≤ (K : ℝ)*‖denseSeq E q‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hf.dist_le_mul (x+denseSeq E q) x
    have hp := metricSeminorm_le hf x (denseSeq E q)
    have hp0 := apply_nonneg (metricSeminorm f x) (denseSeq E q)
    have hd0 := dist_nonneg (x := f (x+denseSeq E q)) (y := f x)
    rw [abs_le]
    constructor <;> nlinarith
  · positivity

omit [MeasurableSpace E] [BorelSpace E] in
lemma bddAbove_metricErrorTerm (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    BddAbove (range (fun q => metricErrorTerm f r q x)) :=
  ⟨2*(K : ℝ), by rintro _ ⟨q,rfl⟩; exact metricErrorTerm_le hf r q x⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_nonneg (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    0 ≤ metricErrorModulus f r x :=
  (metricErrorTerm_nonneg r 0 x).trans (le_ciSup (bddAbove_metricErrorTerm hf r x) 0)

lemma measurable_metricErrorModulus (hf : LipschitzWith K f) (r : ℝ) :
    Measurable (metricErrorModulus f r) := by
  change Measurable (fun x => ⨆ q : ℕ, metricErrorTerm f r q x)
  apply Measurable.iSup
  intro q
  change Measurable (fun x => metricErrorTerm f r q x)
  unfold metricErrorTerm
  split_ifs
  · exact (((hf.continuous.comp (continuous_id.add continuous_const)).dist hf.continuous).measurable.sub
      (measurable_metricSeminorm_apply hf _)).abs.div_const _
  · exact measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_le_of_bound (_hf : LipschitzWith K f) {r ε : ℝ} {x : E}
    (hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ ≤ r → |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ ε*‖v‖) :
    metricErrorModulus f r x ≤ ε := by
  apply ciSup_le
  intro q
  dsimp [metricErrorTerm]
  split_ifs with h
  · exact (div_le_iff₀ h.1).mpr (H _ h.2)
  · exact hε

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_tendsto_zero (hf : LipschitzWith K f) {x : E}
    (hx : HasCenteredMetricDifferential f (metricSeminorm f x) x)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (metricErrorModulus_nonneg hf _ _))
  · intro ε hε
    have hxε := hx.bound (half_pos hε)
    obtain ⟨δ,hδ,hδx⟩ := Metric.mem_nhds_iff.mp hxε
    have hδr := (tendsto_order.1 hr).2 δ hδ
    filter_upwards [hδr] with n hn
    apply lt_of_le_of_lt (metricErrorModulus_le_of_bound hf (half_pos hε).le ?_)
      (half_lt_self hε)
    intro v hv
    have hvδ : x+v ∈ ball x δ := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hv.trans_lt hn
    simpa only [mem_ofPred_eq, add_sub_cancel_left, Real.norm_eq_abs] using hδx hvδ

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_bound (hf : LipschitzWith K f) {r : ℝ} (x v : E)
    (hv : ‖v‖ < r) :
    |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ metricErrorModulus f r x * ‖v‖ := by
  let A : Set E := {w | |dist (f (x+w)) (f x)-metricSeminorm f x w| ≤
    metricErrorModulus f r x * ‖w‖}
  have hA : IsClosed A := isClosed_le
    (((hf.continuous.comp (continuous_const.add continuous_id)).dist continuous_const).sub
      (metricSeminorm_lipschitz hf x).continuous).abs
    (continuous_const.mul continuous_norm)
  have hsub : ball (0 : E) r ∩ range (denseSeq E) ⊆ A := by
    rintro w ⟨hq,⟨q,rfl⟩⟩
    by_cases hw : denseSeq E q = 0
    · simp [A,hw]
    have hqw : 0 < ‖denseSeq E q‖ := norm_pos_iff.mpr hw
    have hqr : ‖denseSeq E q‖ ≤ r := (by simpa only [mem_ball, dist_zero_right] using hq :
      ‖denseSeq E q‖ < r).le
    have hle := le_ciSup (bddAbove_metricErrorTerm hf r x) q
    rw [metricErrorTerm, ite_eq_left ⟨hqw,hqr⟩] at hle
    exact (div_le_iff₀ hqw).mp hle
  have hvcl := (denseRange_denseSeq E).open_subset_closure_inter isOpen_ball
    (by simpa only [mem_ball, dist_zero_right] using hv : v ∈ ball (0 : E) r)
  exact hA.closure_subset_iff.mpr hsub hvcl

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_TwoPoint
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma seminorm_sub_bound_of_sphere {p q : Seminorm ℝ E} {ε : ℝ} (_hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ = 1 → |p v-q v| ≤ ε) (v : E) :
    |p v-q v| ≤ ε*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,hv0.ne']
  have he : ‖v‖ • u = v := by simp [u,hv0.ne']
  have hpv : p v = ‖v‖ * p u := by
    calc p v = p (‖v‖ • u) := congrArg p he.symm
      _ = ‖v‖ * p u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  have hqv : q v = ‖v‖ * q u := by
    calc q v = q (‖v‖ • u) := congrArg q he.symm
      _ = ‖v‖ * q u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  calc |p v-q v| = ‖v‖ * |p u-q u| := by
        rw [hpv,hqv,←mul_sub,abs_mul,abs_of_pos hv0]
    _ ≤ ‖v‖*ε := mul_le_mul_of_nonneg_left (H u hu) hv0.le
    _ = ε*‖v‖ := mul_comm _ _

variable [FiniteDimensional ℝ E]
lemma eventually_seminorm_bound_of_dense
    {ι κ : Type*} {l : Filter ι} {p : ι → Seminorm ℝ E} {q : Seminorm ℝ E}
    {K : ℝ≥0} (hp : ∀ i, LipschitzWith K (p i)) (hq : LipschitzWith K q)
    {D : κ → E} (hD : DenseRange D)
    (hc : ∀ j, Tendsto (fun i => p i (D j)) l (𝓝 (q (D j))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ v : E, |p i v-q v| ≤ ε*‖v‖ := by
  have hlim := tendsto_of_lipschitz_dense hp hq hD hc
  have h := uniformly_tendsto_of_lipschitz hp hq (isCompact_sphere (0 : E) 1)
    (fun v _ => hlim v) hε
  filter_upwards [h] with i hi v
  apply seminorm_sub_bound_of_sphere hε.le _ v
  intro w hw
  exact (hi w (by simpa only [mem_sphere,dist_zero_right] using hw)).le

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma hasTwoPointMetricDifferential_of_uniformModulus
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s) :
    HasTwoPointMetricDifferential f (metricSeminorm f x) s x := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨N,hN⟩ := (eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hu) (ε/2) (half_pos hε)))
  have hNN (y : E) (hy : y ∈ s) : metricErrorModulus f (r N) y < ε/2 := by
    have h := hN N le_rfl y hy
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using h
  have hfst : Tendsto (fun q : E × E => q.1) (𝓝[s ×ˢ s] (x,x)) (𝓝[s] x) :=
    continuous_fst.continuousWithinAt.tendsto_nhdsWithin (fun _ hq => hq.1)
  have hnear : ∀ᶠ q : E × E in 𝓝[s ×ˢ s] (x,x), ‖q.2-q.1‖ < r N := by
    have ht : Tendsto (fun q : E × E => ‖q.2-q.1‖) (𝓝[s ×ˢ s] (x,x)) (𝓝 0) := by
      simpa using ((continuous_snd.sub continuous_fst).norm.continuousWithinAt.tendsto (s := s ×ˢ s) (x := (x,x)))
    exact (tendsto_order.1 ht).2 _ (hr N)
  filter_upwards [hfst.eventually hp,hnear,self_mem_nhdsWithin] with q hqp hqr hqs
  have he₁ := metricErrorModulus_bound hf q.1 (q.2-q.1) hqr
  have he₂ := hqp (q.2-q.1)
  have hm := hNN q.1 hqs.1
  have ht : ‖q.2-q.1‖ ≤ ‖q.1-x‖+‖q.2-x‖ := by
    calc ‖q.2-q.1‖ = ‖(q.2-x)-(q.1-x)‖ := by congr 1; abel
      _ ≤ ‖q.2-x‖+‖q.1-x‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  have he : |dist (f q.1) (f q.2)-metricSeminorm f x (q.1-q.2)| ≤
      ε*(‖q.1-x‖+‖q.2-x‖) := by
    have hpneg : metricSeminorm f x (q.1-q.2) = metricSeminorm f x (q.2-q.1) := by
      rw [←neg_sub q.2 q.1,map_neg_eq_map]
    rw [hpneg,dist_comm]
    calc |dist (f q.2) (f q.1)-metricSeminorm f x (q.2-q.1)| ≤
          |dist (f q.2) (f q.1)-metricSeminorm f q.1 (q.2-q.1)| +
            |metricSeminorm f q.1 (q.2-q.1)-metricSeminorm f x (q.2-q.1)| := abs_sub_le _ _ _
      _ ≤ metricErrorModulus f (r N) q.1 * ‖q.2-q.1‖ + ε/2*‖q.2-q.1‖ := by
        apply add_le_add _ he₂
        simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
      _ ≤ ε*‖q.2-q.1‖ := by nlinarith [norm_nonneg (q.2-q.1)]
      _ ≤ ε*(‖q.1-x‖+‖q.2-x‖) := mul_le_mul_of_nonneg_left ht hε.le
  simpa only [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using he

end SharpIntegralFillings.MetricDifferentiation

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_LargePieces
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SharpIntegralFillings
lemma exists_closed_large_continuousOn
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {f : A → B} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set A, IsClosed K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  let I := countableBasis B
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε I
  have H (i : I) : ∃ U F : Set A,
      f ⁻¹' (i : Set B) ⊆ U ∧ F ⊆ f ⁻¹' (i : Set B) ∧
      IsOpen U ∧ IsClosed F ∧ μ (U \ F) < δ i := by
    let S := f ⁻¹' (i : Set B)
    have hS : MeasurableSet S := hf (isOpen_of_mem_countableBasis i.property).measurableSet
    have hδi : δ i / 2 ≠ 0 := (ENNReal.half_pos (hδ i).ne').ne'
    obtain ⟨U,hSU,hU,_,hμU⟩ := hS.exists_isOpen_sdiff_lt (measure_ne_top μ S) hδi
    obtain ⟨F,hFS,hF,hμF⟩ := hS.exists_isClosed_sdiff_lt (measure_ne_top μ S) hδi
    refine ⟨U,F,hSU,hFS,hU,hF,?_⟩
    calc μ (U \ F) ≤ μ ((U \ S) ∪ (S \ F)) := by
          apply measure_mono
          intro x hx
          by_cases hxs : x ∈ S
          · exact Or.inr ⟨hxs,hx.2⟩
          · exact Or.inl ⟨hx.1,hxs⟩
      _ ≤ μ (U \ S) + μ (S \ F) := measure_union_le _ _
      _ < δ i / 2 + δ i / 2 := ENNReal.add_lt_add hμU hμF
      _ = δ i := ENNReal.add_halves _
  choose U F hSU hFS hU hF hμ using H
  let K : Set A := (⋃ i : I, U i \ F i)ᶜ
  refine ⟨K, (isOpen_iUnion (fun i => (hU i).sdiff (hF i))).isClosed_compl, ?_, ?_⟩
  · calc μ Kᶜ = μ (⋃ i : I, U i \ F i) := by simp [K]
      _ ≤ ∑' i : I, μ (U i \ F i) := measure_iUnion_le _
      _ ≤ ∑' i : I, δ i := ENNReal.tsum_le_tsum (fun i => (hμ i).le)
      _ < ε := hδsum
  · apply (isBasis_countableBasis B).continuousOn_iff.mpr
    intro V hV
    let i : I := ⟨V,hV⟩
    refine ⟨U i,hU i,?_⟩
    ext x
    constructor
    · rintro ⟨hx,hxK⟩
      exact ⟨hSU i hx,hxK⟩
    · rintro ⟨hxU,hxK⟩
      have hxF : x ∈ F i := by
        by_contra h
        exact hxK (mem_iUnion.mpr ⟨i,hxU,h⟩)
      exact ⟨hFS i hxF,hxK⟩

end SharpIntegralFillings

namespace SharpIntegralFillings
open Metric

lemma exists_large_continuousOn_uniformly
    {A B : Type*} [TopologicalSpace A] [PseudoMetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A)
    {s : Set A} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {f : A → B} (hf : Measurable f) {u : ℕ → A → ℝ}
    (hu : ∀ n, Measurable (u n))
    (hc : ∀ᵐ x ∂μ.restrict s, Tendsto (fun n => u n x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ContinuousOn f t ∧ TendstoUniformlyOn u (fun _ => 0) atTop t := by
  let ν := μ.restrict s
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hsf.lt_top⟩
  obtain ⟨K,hK,hμK,hcf⟩ := exists_closed_large_continuousOn ν hf
    (show ENNReal.ofReal (ε/2) ≠ 0 from (ENNReal.ofReal_pos.mpr (half_pos hε)).ne')
  obtain ⟨e,he,hμe,hue⟩ := tendstoUniformlyOn_of_ae_tendsto'
    (fun n => (hu n).stronglyMeasurable) stronglyMeasurable_const hc
    (half_pos hε)
  let t := s ∩ (K \ e)
  refine ⟨t,inter_subset_left,hs.inter (hK.measurableSet.diff he),?_,
    hcf.mono (fun _ h => h.2.1),hue.mono (fun _ h => h.2.2)⟩
  calc μ (s \ t) = ν (Kᶜ ∪ e) := by
        rw [Measure.restrict_apply (hK.measurableSet.compl.union he)]
        congr 1
        ext x
        simp only [t,Set.mem_sdiff,mem_inter_iff,mem_union,mem_compl_iff]
        tauto
    _ ≤ ν Kᶜ + ν e := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hμK.le hμe
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_large_twoPointMetricDifferential
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ x ∈ t, HasTwoPointMetricDifferential f (metricSeminorm f x) t x := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  obtain ⟨t,hts,ht,hμt,hct,htu⟩ := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x j => metricSeminorm f x (denseSeq E j)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun n => measurable_metricErrorModulus hf (r n)) hc hε
  refine ⟨t,hts,ht,hμt,?_⟩
  intro x hx
  apply hasTwoPointMetricDifferential_of_uniformModulus hf _ hr htu
  intro j
  exact (continuousOn_pi.1 hct j) x hx

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Density
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

namespace SharpIntegralFillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma tangentConeAt_pi_eq_univ_of_density_one {ι : Type*} [Fintype ι]
    (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    tangentConeAt ℝ {f : ι → E | ∀ i, f i ∈ s} (fun _ => x) = univ := by
  classical
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ i, (s ∩ ({x} + r • closedBall (z i) (ε / 2))).Nonempty := by
    rw [eventually_all]
    intro i
    exact Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _
      measurableSet_closedBall (measure_closedBall_pos μ (z i) (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : ι → E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, hr₁, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  have H (i : ι) : ∃ a ∈ closedBall (z i) (ε / 2), x + r • a ∈ s := by
    obtain ⟨y, hys, hy⟩ := hr₁ i
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    simpa only [h, add_neg_cancel_left] using hys
  choose a ha has using H
  have haz : a ∈ closedBall z (ε / 2) := by
    rw [mem_closedBall, dist_pi_le_iff (half_pos hε).le]
    exact ha
  refine ⟨a, ?_, ?_⟩
  · have hra : r • a ∈ U ∩ ((fun _ : ι => x) + ·) ⁻¹' {f | ∀ i, f i ∈ s} := by
      exact ⟨hrU (smul_mem_smul_set haz), has⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ (ne_of_gt hr) a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using haz) (half_lt_self hε)

omit [MeasurableSpace E] [BorelSpace E] in

lemma seminorm_continuous_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  classical
  let b := Module.finBasis ℝ E
  have hsum (I : Finset (Fin (Module.finrank ℝ E)))
      (q : Fin (Module.finrank ℝ E) → E) :
      p (∑ i ∈ I, q i) ≤ ∑ i ∈ I, p (q i) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hb (v : E) : p v ≤ ∑ i, ‖b.repr v i‖ * p (b i) := by
    convert hsum Finset.univ (fun i => b.repr v i • b i) using 1
    · rw [b.sum_repr]
    · simp only [map_smul_eq_mul]
  have hcont : Continuous (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp b.continuous_coe_repr).norm.mul_const _
  apply Seminorm.continuous_of_continuousAt_zero
  have hc : Tendsto (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  simpa [ContinuousAt] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc (fun v => apply_nonneg p v) hb

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Geometry_Comparison
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

namespace SharpIntegralFillings
universe u

theorem IsCAT0.exists_squared_distance_convex
    {X : Type u} [MetricSpace X] (hX : IsCAT0 X) :
    ∃ segment : X → X → ℝ → X,
      (∀ x y, segment x y 0 = x ∧ segment x y 1 = y) ∧
      ∀ o y x t, t ∈ Icc (0 : ℝ) 1 →
        dist (segment o y t) x ^ 2 ≤
          (1 - t) * dist o x ^ 2 + t * dist y x ^ 2 -
            t * (1 - t) * dist o y ^ 2 := by
  obtain ⟨s, hs, _, hc⟩ := hX
  refine ⟨s, hs, ?_⟩
  intro o y x t ht
  have h := hc o y x t 1 ht (by simp)
  rw [(hs o x).2] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem IsCAT0.quadrilateral {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  obtain ⟨s, _, hs⟩ := hX.exists_squared_distance_convex
  have hb := hs a c b (1 / 2) (by norm_num)
  have hd := hs a c d (1 / 2) (by norm_num)
  have ht := dist_triangle b (s a c (1 / 2)) d
  have ht' : dist b d ^ 2 ≤
      (dist b (s a c (1 / 2)) + dist (s a c (1 / 2)) d) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (add_nonneg dist_nonneg dist_nonneg)).mpr ht
  have hm := sq_nonneg (dist b (s a c (1 / 2)) - dist (s a c (1 / 2)) d)
  rw [dist_comm c b] at hb
  rw [dist_comm a d] at hd
  rw [dist_comm b (s a c (1 / 2))] at ht' hm
  nlinarith

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Parallelogram
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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

namespace SharpIntegralFillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
section MetricDifferential
variable {X : Type*} [MetricSpace X]
omit [MeasurableSpace E] [BorelSpace E] in

lemma HasTwoPointMetricDifferential.scaled_pair_limit
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x u v : E}
    (h : HasTwoPointMetricDifferential f p s x)
    {c : ℕ → ℝ} {d e : ℕ → E}
    (hc : Tendsto (fun j => ‖c j‖) atTop atTop)
    (hd : ∀ᶠ j in atTop, x + d j ∈ s) (he : ∀ᶠ j in atTop, x + e j ∈ s)
    (hcd : Tendsto (fun j => c j • d j) atTop (𝓝 u))
    (hce : Tendsto (fun j => c j • e j) atTop (𝓝 v)) :
    Tendsto (fun j => ‖c j‖ * dist (f (x + d j)) (f (x + e j)))
      atTop (𝓝 (p (u - v))) := by
  have hp := seminorm_continuous_finiteDimensional p
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have he₀ := tangentConeAt.lim_zero atTop hc hce
  have hpair : Tendsto (fun j => (x + d j, x + e j)) atTop (𝓝[s ×ˢ s] (x,x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds.add hd₀).prodMk_nhds (tendsto_const_nhds.add he₀)
    · filter_upwards [hd, he] with j hj hj'
      exact ⟨hj, hj'⟩
  have hsmall := h.comp_tendsto hpair
  have hmul := hsmall.mul_isBigO (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => (‖(x + d j) - x‖ + ‖(x + e j) - x‖) * ‖c j‖)
      atTop (𝓝 (‖u‖ + ‖v‖)) := by
    simpa only [norm_smul, add_sub_cancel_left, add_mul, mul_comm] using hcd.norm.add hce.norm
  have hzero := hmul.tendsto_zero_of_tendsto hnorm
  have hdiff := hp.tendsto (u - v) |>.comp (hcd.sub hce)
  have hsum := hzero.add hdiff
  convert hsum using 1
  · ext j
    simp only [Function.comp_apply, add_sub_add_left_eq_sub, ← smul_sub, map_smul_eq_mul]
    ring
  · simp

lemma HasTwoPointMetricDifferential.distance_bound
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) (w : E) :
    A * ‖w‖ ≤ B * p w := by
  let z : Fin 2 → E := ![w, 0]
  have hz : z ∈ tangentConeAt ℝ {f : Fin 2 → E | ∀ i, f i ∈ s} (fun _ => x) := by
    rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
    exact mem_univ z
  obtain ⟨c, d, hc, hd, hcd⟩ :=
    mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
  have hcd₀ := tendsto_pi_nhds.mp hcd 0
  have hcd₁ := tendsto_pi_nhds.mp hcd 1
  have hl := h.scaled_pair_limit hc (hd.mono fun _ hj => hj 0)
    (hd.mono fun _ hj => hj 1) hcd₀ hcd₁
  have hl' : Tendsto (fun j => ‖c j‖ * dist (f (x + d j 0)) (f (x + d j 1)))
      atTop (𝓝 (p w)) := by simpa [z] using hl
  have hr : Tendsto (fun j => ‖c j‖ * dist (x + d j 0) (x + d j 1))
      atTop (𝓝 ‖w‖) := by
    simpa only [Pi.smul_apply, dist_eq_norm, add_sub_add_left_eq_sub, ← norm_smul, smul_sub,
      z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
      using (hcd₀.sub hcd₁).norm
  apply le_of_tendsto_of_tendsto (hr.const_mul A) (hl'.const_mul B)
  filter_upwards [hd] with j hj
  have H := mul_le_mul_of_nonneg_left
    (hAB (x + d j 0) (hj 0) (x + d j 1) (hj 1)) (norm_nonneg (c j))
  simpa only [mul_left_comm] using H

end MetricDifferential
end SharpIntegralFillings

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {X : Type*} [MetricSpace X]

lemma HasTwoPointMetricDifferential.parallelogram_of_quadrilateralOn
    {f : E → X} {p : Seminorm ℝ E} {s : Set E} {x : E}
    (h : HasTwoPointMetricDifferential f p s x)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (u v : E) :
    p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2 := by
  have hle (u v : E) : p (u+v)^2+p (u-v)^2 ≤ 2*p u^2+2*p v^2 := by
    let z : Fin 4 → E := ![0,u,u+v,v]
    have hz : z ∈ tangentConeAt ℝ {f : Fin 4 → E | ∀ i, f i ∈ s} (fun _ => x) := by
      rw [tangentConeAt_pi_eq_univ_of_density_one μ s x hx]
      exact mem_univ z
    obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hz
    have hl (i j : Fin 4) :
        Tendsto (fun k => ‖c k‖*dist (f (x+d k i)) (f (x+d k j))) atTop (𝓝 (p (z i-z j))) := by
      apply h.scaled_pair_limit hc
      · filter_upwards [hd] with k hk
        exact hk i
      · filter_upwards [hd] with k hk
        exact hk j
      · exact tendsto_pi_nhds.mp hcd i
      · exact tendsto_pi_nhds.mp hcd j
    have hquad : ∀ᶠ k in atTop,
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 3)))^2 ≤
        (‖c k‖*dist (f (x+d k 0)) (f (x+d k 1)))^2 +
        (‖c k‖*dist (f (x+d k 1)) (f (x+d k 2)))^2 +
        (‖c k‖*dist (f (x+d k 2)) (f (x+d k 3)))^2 +
        (‖c k‖*dist (f (x+d k 3)) (f (x+d k 0)))^2 := by
      filter_upwards [hd] with k hk
      have H := hQ _ (hk 0) _ (hk 1) _ (hk 2) _ (hk 3)
      simpa only [Pi.add_apply,mul_add,mul_pow] using mul_le_mul_of_nonneg_left H (sq_nonneg ‖c k‖)
    have H := le_of_tendsto_of_tendsto
      (((hl 0 2).pow 2).add ((hl 1 3).pow 2))
      (((((hl 0 1).pow 2).add ((hl 1 2).pow 2)).add ((hl 2 3).pow 2)).add ((hl 3 0).pow 2)) hquad
    have hneg : p (-u+-v) = p (u+v) := by rw [←neg_add,map_neg_eq_map]
    simpa [z,map_neg_eq_map,hneg,two_mul,add_assoc,add_left_comm,add_comm] using H
  have hf := hle u v
  have hr := hle (u+v) (u-v)
  have he₁ : (u+v)+(u-v) = (2 : ℝ) • u := by module
  have he₂ : (u+v)-(u-v) = (2 : ℝ) • v := by module
  rw [he₁,he₂,map_smul_eq_mul,map_smul_eq_mul] at hr
  norm_num at hr
  linarith
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_HilbertCharts
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

namespace SharpIntegralFillings
lemma ae_restrict_of_arbitrarily_large_pieces
    {A : Type*} [MeasurableSpace A] (μ : Measure A) {s : Set A} (hs : MeasurableSet s)
    {P : A → Prop}
    (H : ∀ ε : ℝ, 0 < ε → ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ∀ᵐ x ∂μ.restrict t, P x) :
    ∀ᵐ x ∂μ.restrict s, P x := by
  apply (ae_restrict_iff' hs).2
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨t,_,ht,htμ,hP⟩ := H ε hε
  have hnull : μ {x | ¬(x ∈ t → P x)} = 0 := ae_iff.1 ((ae_restrict_iff' ht).1 hP)
  calc μ {x | ¬(x ∈ s → P x)} ≤ μ ((s \ t) ∪ {x | ¬(x ∈ t → P x)}) := by
        apply measure_mono
        intro x hx
        simp only [mem_ofPred_eq, Classical.not_imp] at hx
        by_cases hxt : x ∈ t
        · exact Or.inr (by simpa only [mem_ofPred_eq, Classical.not_imp] using And.intro hxt hx.2)
        · exact Or.inl ⟨hx.1,hxt⟩
    _ ≤ μ (s \ t) + μ {x | ¬(x ∈ t → P x)} := measure_union_le _ _
    _ ≤ 0+(ε : ENNReal) := by simpa only [hnull,add_zero,zero_add,ENNReal.ofReal_coe_nnreal] using htμ
end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_parallelogram_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    (hQ : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (f a) (f c)^2 + dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2 + dist (f b) (f c)^2 + dist (f c) (f d)^2 + dist (f d) (f a)^2) :
    ∀ᵐ x ∂μ.restrict s, ∀ u v : E,
      metricSeminorm f x (u+v)^2+metricSeminorm f x (u-v)^2 =
        2*metricSeminorm f x u^2+2*metricSeminorm f x v^2 := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd u v
  exact (hD x hx).parallelogram_of_quadrilateralOn μ
    (fun a ha b hb c hc d hd => hQ a (hts ha) b (hts hb) c (hts hc) d (hts hd)) hxd u v
end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem ae_metricSeminorm_distance_bound_on
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {A B : ℝ}
    (hAB : ∀ a ∈ s, ∀ b ∈ s, A * dist a b ≤ B * dist (f a) (f b)) :
    ∀ᵐ x ∂μ.restrict s, ∀ w : E, A * ‖w‖ ≤ B * metricSeminorm f x w := by
  apply ae_restrict_of_arbitrarily_large_pieces μ hs
  intro ε hε
  obtain ⟨t,hts,ht,htμ,hD⟩ := exists_large_twoPointMetricDifferential μ hf hs hsf hε
  refine ⟨t,hts,ht,htμ,?_⟩
  filter_upwards [ae_restrict_mem ht, Besicovitch.ae_tendsto_measure_inter_div μ t] with x hx hxd w
  exact (hD x hx).distance_bound μ hxd
    (fun a ha b hb => hAB a (hts ha) b (hts hb)) w
end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_LocalBounds
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma seminorm_le_of_centered_bound {s : Set E} {x : E}
    {r : E → ℝ} {p q : Seminorm ℝ E} {B : ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (hbound : ∀ y ∈ s, r y ≤ B*q (y-x)) (v : E) : p v ≤ B*q v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  have hlim : Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
    convert hzero.add hp using 1
    · ext j
      simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
      ring
    · simp
  have hq : Tendsto (fun j => B*(‖c j‖*q (d j))) atTop (𝓝 (B*q v)) := by
    simpa only [Function.comp_apply,map_smul_eq_mul] using
      (((seminorm_continuous_finiteDimensional q).tendsto v).comp hcd).const_mul B
  apply le_of_tendsto_of_tendsto hlim hq
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [add_sub_cancel_left,mul_left_comm] using hh

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.seminorm_le_on_piece
    {s t : Set E} (hts : t ⊆ s) {f : s → X} {p q : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun r => μ (t ∩ closedBall (x : E) r) / μ (closedBall (x : E) r))
      (𝓝[>] 0) (𝓝 1)) {B : ℝ}
    (hb : ∀ y (hy : y ∈ t), dist (f ⟨y,hts hy⟩) (f x) ≤ B*q (y-(x : E))) :
    ∀ v : E, p v ≤ B*q v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property,Asymptotics.isLittleO_map]
    simpa only [HasCenteredMetricDifferentialWithin,Function.comp_def,r,
      dite_eq_left (Subtype.coe_prop _),Subtype.coe_eta] using h
  apply seminorm_le_of_centered_bound μ hx (hr.mono (nhdsWithin_mono _ hts))
  intro y hy
  simpa only [r,dite_eq_left (hts hy)] using hb y hy

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_HilbertMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
open Matrix MeasureTheory Set Filter
open scoped MatrixOrder NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma hilbert_piece_mass_le
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (p : Euc k → Seminorm ℝ (Euc k)) (q : Seminorm ℝ (Euc k))
    (hq : ∀ v, q v = 0 ↔ v = 0)
    (hqpara : ∀ u v, q (u+v)^2+q (u-v)^2 = 2*q u^2+2*q v^2)
    (hp : ∀ᵐ z ∂volume.restrict t,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ v, p z v = 0 ↔ v = 0) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2))
    (K L : ℝ≥0)
    (hnear : ∀ y (hy : y ∈ t) z (hz : z ∈ t),
      q (y-z) ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) ∧
      dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) ≤ (L : ℝ)*q (y-z)) :
    densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| *
        Real.sqrt (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      ≤ (((L*K)^k) • ν).restrict (C.paramExtended '' t) := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix q b
  let Jq := Real.sqrt Q.det
  have hQ : Q.PosDef := polarizationMatrix_posDef b q hq hqpara
  let ℓ : Fin k → Euc k →L[ℝ] ℝ := fun i => matrixRowFunctional (CFC.sqrt Q) i
  have hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y-ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩) := by
    intro i y hy z hz
    rw [←map_sub]
    apply (abs_matrixRow_sqrt_le Q hQ.posSemidef i (y-z)).trans
    simpa only [Q,b,sqrt_polarization_quadratic q hq hqpara,WithLp.toLp_ofLp] using
      (hnear y hy z hz).1
  have hm : (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)) = CFC.sqrt Q := by
    ext i j
    simp only [ℓ,Matrix.of_apply,matrixRowFunctional_single]
  have hdet : |(CFC.sqrt Q).det| = Jq := by
    rw [show (CFC.sqrt Q).det = Real.sqrt Q.det by simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hpiece : densityPush (volume.restrict t) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| * Jq) ≤ ((K^k) • ν).restrict (C.paramExtended '' t) := by
    simpa only [hm,hdet] using C.linear_piece_mass_le hC hν ht hts ℓ K hrow
  have hJ : ∀ᵐ z ∂volume.restrict t,
      Real.sqrt (polarizationMatrix (p z) b).det ≤ (L : ℝ)^k * Jq := by
    filter_upwards [hp,ae_restrict_mem ht,Besicovitch.ae_tendsto_measure_inter_div volume t]
      with z hz hzt hzd
    apply sqrt_det_polarization_le (p z) q hz.2.1 hq hz.2.2 hqpara L.coe_nonneg
    apply (hz.1 (hts hzt)).seminorm_le_on_piece volume hts hzd
    intro y hy
    exact (hnear y hy z hzt).2
  calc
    _ ≤ densityPush (volume.restrict t) C.paramExtended
        (fun z => ((L^k : ℝ≥0) : ℝ) * (|(C.multiplicity z : ℝ)| * Jq)) := by
      apply densityPush_mono_ae C.measurable_paramExtended
      filter_upwards [hJ] with z hz
      have hh := mul_le_mul_of_nonneg_left hz (abs_nonneg (C.multiplicity z : ℝ))
      simpa only [NNReal.coe_pow,mul_left_comm] using hh
    _ = (L^k) • densityPush (volume.restrict t) C.paramExtended
        (fun z => |(C.multiplicity z : ℝ)| * Jq) := densityPush_const_mul _ _ _ _
    _ ≤ (L^k) • (((K^k) • ν).restrict (C.paramExtended '' t)) := by
      exact smul_le_smul_left (L^k) hpiece
    _ = (((L*K)^k) • ν).restrict (C.paramExtended '' t) := by
      rw [Measure.restrict_smul,smul_smul,←mul_pow,←Measure.restrict_smul]

end IntegerChart
end SharpIntegralFillings

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma measure_le_of_nearIsometry_factors {β : Type*} [MeasurableSpace β]
    {μ ν : Measure β} [IsFiniteMeasure ν] (k : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 →
      μ ≤ ENNReal.ofReal (((1+ε)/(1-ε))^k) • ν) : μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1+ε)/(1-ε))^k))
      (𝓝[>] 0) (𝓝 1) := by
    have hd : ContinuousAt (fun ε : ℝ => ((1+ε)/(1-ε))^k) 0 := by
      fun_prop (disch := norm_num)
    have hh := ENNReal.continuous_ofReal.continuousAt.comp (x := 0) hd
    simpa only [Function.comp_def,add_zero,sub_zero,div_one,one_pow,ENNReal.ofReal_one] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hv : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1+ε)/(1-ε))^k)*ν s)
      (𝓝[>] 0) (𝓝 (ν s)) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr (measure_ne_top ν s))
  apply ge_of_tendsto hv
  have hε0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hε1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hε0,hε1] with ε hε hε'
  simpa only [Measure.smul_apply,smul_eq_mul] using h ε hε hε' s

end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Partitions
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
lemma exists_radius_uniform_metric_error
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤ ε*‖y-z‖ := by
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨a,ha,hap⟩ := Metric.mem_nhdsWithin_iff.1 hp
  obtain ⟨N,hN⟩ := (eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu (ε/2) (half_pos hε)))
  have hNN := hN N le_rfl
  refine ⟨min a (r N/3), lt_min ha (div_pos (hr N) (by norm_num)), ?_⟩
  intro y hy z hz
  have hyp : ∀ v : E, |metricSeminorm f y v-metricSeminorm f x v| ≤ ε/2*‖v‖ :=
    hap ⟨show dist y x < a from lt_of_lt_of_le hy.2 (min_le_left _ _),hy.1⟩
  have hyz : ‖z-y‖ < r N := by
    have h₁ : ‖y-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hy.2) (min_le_right _ _)
    have h₂ : ‖z-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hz.2) (min_le_right _ _)
    have h₃ : ‖z-y‖ ≤ ‖z-x‖+‖y-x‖ := by
      calc ‖z-y‖ = ‖(z-x)-(y-x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith [hr N]
  have he₁ := metricErrorModulus_bound hf y (z-y) hyz
  have he₂ := hyp (z-y)
  have hm : metricErrorModulus f (r N) y < ε/2 := by
    have hm := hNN y hy.1
    simpa only [dist_zero_left,Real.norm_eq_abs,
      abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using hm
  have hpneg : metricSeminorm f x (y-z) = metricSeminorm f x (z-y) := by
    rw [←neg_sub z y,map_neg_eq_map]
  rw [hpneg,dist_comm,norm_sub_rev]
  calc |dist (f z) (f y)-metricSeminorm f x (z-y)| ≤
        |dist (f z) (f y)-metricSeminorm f y (z-y)| +
          |metricSeminorm f y (z-y)-metricSeminorm f x (z-y)| := abs_sub_le _ _ _
    _ ≤ metricErrorModulus f (r N) y*‖z-y‖+ε/2*‖z-y‖ := by
      apply add_le_add _ he₂
      simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
    _ ≤ ε*‖z-y‖ := by nlinarith [norm_nonneg (z-y)]

lemma exists_radius_nearIsometric
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      (1-ε)*metricSeminorm f x (y-z) ≤ dist (f y) (f z) ∧
      dist (f y) (f z) ≤ (1+ε)*metricSeminorm f x (y-z) := by
  obtain ⟨δ,hδ,H⟩ := exists_radius_uniform_metric_error hf hc hr hu (div_pos hε hA)
  refine ⟨δ,hδ,?_⟩
  intro y hy z hz
  have he : |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤
      ε*metricSeminorm f x (y-z) := by
    apply (H y hy z hz).trans
    calc (ε/A)*‖y-z‖ ≤ (ε/A)*(A*metricSeminorm f x (y-z)) :=
          mul_le_mul_of_nonneg_left (hbound _) (div_pos hε hA).le
      _ = ε*metricSeminorm f x (y-z) := by field_simp
  obtain ⟨hl,hr⟩ := abs_le.1 he
  constructor <;> linarith

lemma exists_nearIsometric_partition
    [MeasurableSpace E] [BorelSpace E] {s : Set E} [Nonempty s]
    (hs : MeasurableSet s) (hf : LipschitzWith K f)
    (hc : ∀ x ∈ s, ∀ j : ℕ, ContinuousWithinAt
      (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → s) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (⋃ i, t i) = s ∧ ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  choose δ hδ hlocal using fun x : s =>
    exists_radius_nearIsometric hf (hc x x.property) hr hu hA (hbound x x.property) hε
  obtain ⟨c,hcvr⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    (fun x : s => ball (x : E) (δ x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨⟨x,hx⟩,mem_ball_self (hδ ⟨x,hx⟩)⟩)
  let t : ℕ → Set E := fun i => s ∩ ball (c i : E) (δ (c i))
  refine ⟨c,disjointed t, fun i => MeasurableSet.disjointed
    (fun j => hs.inter isOpen_ball.measurableSet) i,disjoint_disjointed t,?_,?_⟩
  · rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset (fun i => inter_subset_left)
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.1 (hcvr hx)
      exact mem_iUnion.2 ⟨i,hx,hi⟩
  · intro i y hy z hz
    exact hlocal (c i) y (disjointed_le t i hy) z (disjointed_le t i hz)

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_nearIsometric_partition
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  let r : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  have H (j : ℕ) := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x i => metricSeminorm f x (denseSeq E i)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun i => measurable_metricErrorModulus hf (r i)) hc (hr j)
  choose u hus hum hμu hcu huu using H
  have HP (j : ℕ) : ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (⋃ i, t i) = u j ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
    by_cases hne : (u j).Nonempty
    · let _ : Nonempty (u j) := hne.to_subtype
      obtain ⟨c,t,ht,_,htu,hineq⟩ := exists_nearIsometric_partition (hum j) hf
        (fun x hx i => (continuousOn_pi.1 (hcu j) i) x hx) hr (huu j) hA
        (fun x hx => hbound x (hus j hx)) hε
      exact ⟨fun i => c i,t,ht,htu,fun i _ => hus j (c i).property,hineq⟩
    · refine ⟨fun _ => 0,fun _ => ∅,fun _ => MeasurableSet.empty,?_,?_,?_⟩
      · simp [not_nonempty_iff_eq_empty.mp hne]
      · simp
      · simp
  choose c t htm htunion hcs htineq using HP
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let T : ℕ → Set E := fun i => t (e i).1 (e i).2
  have hTunion : (⋃ i, T i) = ⋃ j, u j := by
    ext x
    simp only [T,mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,htunion (e i).1 ▸ mem_iUnion.2 ⟨(e i).2,hi⟩⟩
    · rintro ⟨j,hj⟩
      obtain ⟨i,hi⟩ := mem_iUnion.1 ((htunion j).symm ▸ hj)
      refine ⟨e.symm (j,i),?_⟩
      simpa using hi
  have hu0 : μ (s \ ⋃ j, u j) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto (by simpa using ENNReal.tendsto_ofReal hr0)
    filter_upwards [] with j
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion u j))).trans (hμu j)
  refine ⟨fun i => c (e i).1 (e i).2,disjointed T,
    fun i => MeasurableSet.disjointed (fun k => htm (e k).1 (e k).2) i,
    ?_,disjoint_disjointed T,?_,?_,?_⟩
  · intro i x hx
    apply hus (e i).1
    rw [←htunion (e i).1]
    exact mem_iUnion.2 ⟨(e i).2,disjointed_le T i hx⟩
  · rw [iUnion_disjointed,hTunion]
    exact hu0
  · intro i hi
    exact hcs _ _ (hi.mono (disjointed_le T i))
  · intro i y hy z hz
    exact htineq _ _ y (disjointed_le T i hy) z (disjointed_le T i hz)

end SharpIntegralFillings.MetricDifferentiation
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_HilbertPartition
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

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
theorem exists_ae_nearIsometric_partition_with_property
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {P : E → Prop} (hP : ∀ᵐ x ∂μ.restrict s, P x)
    {A : ℝ} (hA : 0 < A)
    (hbound : ∀ x ∈ s, P x → ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s ∧ P (c i)) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  have hnull : μ {x | ¬(x ∈ s → P x)} = 0 :=
    ae_iff.mp ((ae_restrict_iff' hs).mp hP)
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null hnull
  let s₀ := s \ N
  have hs₀ : MeasurableSet s₀ := hs.diff hNm
  have hprop : ∀ x ∈ s₀, P x := by
    intro x hx
    by_contra hp
    exact hx.2 (hN (by simpa using And.intro hx.1 hp))
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition μ hf hs₀
      ((measure_mono sdiff_subset).trans_lt hsf.lt_top).ne hA
      (fun x hx => hbound x hx.1 (hprop x hx)) hε
  refine ⟨c,t,htm,fun i => (hts i).trans sdiff_subset,hdisj,?_,?_,hineq⟩
  · apply le_antisymm _ bot_le
    calc μ (s \ ⋃ i, t i) ≤ μ (N ∪ (s₀ \ ⋃ i, t i)) := by
          apply measure_mono
          intro x hx
          by_cases hn : x ∈ N
          · exact Or.inl hn
          · exact Or.inr ⟨⟨hx.1,hn⟩,hx.2⟩
      _ ≤ μ N + μ (s₀ \ ⋃ i, t i) := measure_union_le _ _
      _ = 0 := by rw [hN0,ht0,add_zero]
  · intro i hi
    exact ⟨(hcs i hi).1,hprop _ (hcs i hi)⟩

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]

theorem exists_hilbertian_nearIsometric_chart_partition
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞) {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hJ : AntilipschitzWith J f)
    (hQ : ∀ a b c d : s,
      dist (f a) (f c)^2+dist (f b) (f d)^2 ≤
        dist (f a) (f b)^2+dist (f b) (f c)^2+dist (f c) (f d)^2+dist (f d) (f a)^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (p : ℕ → Seminorm ℝ E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, LipschitzWith K (p i)) ∧
      (∀ i, (t i).Nonempty →
        (∀ u v, p i (u+v)^2+p i (u-v)^2 = 2*p i u^2+2*p i v^2) ∧
        (∀ v, ‖v‖ ≤ (J : ℝ)*p i v)) ∧
      ∀ i, ∀ y : s, (y : E) ∈ t i → ∀ z : s, (z : E) ∈ t i →
        (1-ε)*p i ((y : E)-(z : E)) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*p i ((y : E)-(z : E)) := by
  classical
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    exact hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  have hQG : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, ∀ d ∈ s,
      dist (G a) (G c)^2+dist (G b) (G d)^2 ≤
        dist (G a) (G b)^2+dist (G b) (G c)^2+dist (G c) (G d)^2+dist (G d) (G a)^2 := by
    intro a ha b hb c hc d hd
    simpa only [← hdist] using hQ ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩
  have hJG : ∀ a ∈ s, ∀ b ∈ s, (1 : ℝ)*dist a b ≤ (J : ℝ)*dist (G a) (G b) := by
    intro a ha b hb
    have hh := hJ.le_mul_dist ⟨a,ha⟩ ⟨b,hb⟩
    change dist a b ≤ (J : ℝ)*dist (f ⟨a,ha⟩) (f ⟨b,hb⟩) at hh
    simpa only [←hdist,one_mul] using hh
  let P : E → Prop := fun x =>
    (∀ u v, metricSeminorm G x (u+v)^2+metricSeminorm G x (u-v)^2 =
      2*metricSeminorm G x u^2+2*metricSeminorm G x v^2) ∧
    (∀ v, ‖v‖ ≤ (J : ℝ)*metricSeminorm G x v)
  have hP : ∀ᵐ x ∂μ.restrict s, P x := by
    filter_upwards [ae_metricSeminorm_parallelogram_on μ hG hs hsf hQG,
      ae_metricSeminorm_distance_bound_on μ hG hs hsf hJG] with x hx hj
    exact ⟨hx,by simpa only [one_mul] using hj⟩
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition_with_property μ hG hs hsf hP
      (A := (J : ℝ)+1) (by positivity)
      (fun x _ hx v => (hx.2 v).trans <| mul_le_mul_of_nonneg_right
        (by linarith) (apply_nonneg (metricSeminorm G x) v)) hε
  refine ⟨fun i => metricSeminorm G (c i),t,htm,hts,hdisj,ht0,
    fun i => metricSeminorm_lipschitz hG (c i),fun i hi => (hcs i hi).2,?_⟩
  intro i y hy z hz
  simpa only [hdist] using hineq i y hy z hz
end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_ExactMass
attribute [-instance] _root_.OAI.SharpIntegralFillings.MassMeasure.currentMassMeasure_finite _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
lemma hilbert_mass_measure_le_oai (hX : IsCAT0 X)
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ v, p z v = 0 ↔ v = 0) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2)) :
    C.majorantMeasure (fun z => Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) ≤ ν := by
  obtain ⟨A,B,hA,hB⟩ := C.bilipschitz
  apply measure_le_of_nearIsometry_factors k
  intro ε hε hε1
  let L : ℝ≥0 := ⟨1+ε,by linarith⟩
  let K : ℝ≥0 := ⟨(1-ε)⁻¹, inv_nonneg.mpr (by linarith)⟩
  have hcoeff : ENNReal.ofReal (((1+ε)/(1-ε))^k) = ((L*K)^k : ℝ≥0) := by
    rw [←ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hcoeff]
  change _ ≤ ((L*K)^k) • ν
  obtain ⟨q,t,ht,hts,hdisj,hnull,_,hq,hnear⟩ :=
    MetricDifferentiation.exists_hilbertian_nearIsometric_chart_partition volume
      C.borel C.bounded.measure_lt_top.ne hA hB
      (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d)) hε
  apply densityPush_le_of_partition C.measurable_paramExtended _ ht hts hdisj hnull
    (fun i => C.measurableSet_paramExtended_image (ht i) (hts i))
  · intro x hx y hy hxy
    exact congrArg (fun z : C.domain => (z : Euc k)) (hB.injective
      (show C.param ⟨x,hx⟩ = C.param ⟨y,hy⟩ from by
        simpa only [paramExtended,dite_eq_left hx,dite_eq_left hy] using hxy))
  intro i
  by_cases hi : (t i).Nonempty
  · have hq0 : ∀ v, q i v = 0 ↔ v = 0 := by
      intro v
      constructor
      · intro hv
        have hh := (hq i hi).2 v
        rw [hv,mul_zero] at hh
        exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
      · rintro rfl
        exact map_zero _
    apply C.hilbert_piece_mass_le hC hν (ht i) (hts i) p (q i) hq0 (hq i hi).1
      (hp.filter_mono (ae_mono (Measure.restrict_mono (hts i) le_rfl))) K L
    intro y hy z hz
    have hh := hnear i ⟨y,hts i hy⟩ hy ⟨z,hts i hz⟩ hz
    refine ⟨?_,hh.2⟩
    change q i (y-z) ≤ (1-ε)⁻¹ * _
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    simpa only [mul_comm] using hh.1
  · have he : t i = ∅ := Set.not_nonempty_iff_eq_empty.mp hi
    simp only [he,Measure.restrict_empty,densityPush_eq_map _ C.measurable_paramExtended,
      withDensity_zero_left,Measure.map_zero,
      image_empty,le_refl]

end IntegerChart
end SharpIntegralFillings

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SharpIntegralFillings.IntegerChart.hilbert_mass_measure_le_oai.{u_1} := @OAI.SharpIntegralFillings.IntegerChart.hilbert_mass_measure_le_oai.{u_1}
