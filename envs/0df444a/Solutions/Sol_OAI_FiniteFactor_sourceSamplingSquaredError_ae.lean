-- Prove2me | solution 1 for OAI.FiniteFactor.sourceSamplingSquaredError_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:45:09.7113+00:00
-- url     : https://prove2.me/submissions/4258ef85-cf28-467b-a193-e1123d45ac89

import Mathlib
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceSampling_coordinate_pair_error

section
-- module Solutions.OAIQ3_FF.Compat
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Density
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Finite product estimate used in uniform-product-density; the bound has
no dependence on the choice of endpoint orientation. -/
theorem product_energy_le_exp {ι : Type*} [Fintype ι]
    (A e : ι → ℝ) (hA0 : ∀ i, 0 ≤ A i) (hA : ∀ i, A i ≤ 1 + e i) :
    (∏ i, A i) ≤ Real.exp (∑ i, e i) := by
  calc
    (∏ i, A i) ≤ ∏ i, Real.exp (e i) := by
      apply Finset.prod_le_prod (fun i _ => hA0 i)
      intro i _
      exact (hA i).trans (by linarith [Real.add_one_le_exp (e i)])
    _ = _ := (Real.exp_sum _ _).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Prefix
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

/-- Finite-coordinate factorization under the actual infinite product measure. -/
theorem integral_infinitePi_finset_prod {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i)) :
    (∫ x, ∏ i ∈ I, f i (x i) ∂Measure.infinitePi μ) = ∏ i ∈ I, ∫ t, f i t ∂μ i := by
  classical
  have he (x : ∀ i, X i) : (∏ i ∈ I, f i (x i)) = ∏ i : I, f i (x i) :=
    (Finset.prod_coe_sort I (fun i => f i (x i))).symm
  simp_rw [he]
  change (∫ x, (∏ i : I, f i (I.restrict x i)) ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi μ
    (f := fun x : ∀ i : I, X i => ∏ i : I, f i (x i))
    ((Finset.measurable_prod _ fun (i : I) _ => (hf i).comp (measurable_pi_apply i)).aestronglyMeasurable)]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort I (fun i => ∫ t, f i t ∂μ i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BlockLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section
namespace CouplingParameters

theorem mem_blockPrefix (m : ℕ → ℕ) (n : ℕ) (i : BlockCoordinate m) :
    i ∈ blockPrefix m n ↔ i.1 < n := by simp [blockPrefix]

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Stages
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter Finset
open scoped Topology
noncomputable section

theorem sourceStage_previous_size (s : ℕ) :
    (sourceStageState s).d = ∑ t ∈ Finset.range s, (sourceStage t).m := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [Finset.sum_range_succ, sourceStageState, SourceStageChoice.next, sourceStage] using congrArg (fun x => x+(sourceStage s).m) ih

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AngleLaw
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceAngleUnit_pos (i : SourceCoordinate) : 0 < sourceAngleUnit i :=
  one_div_pos.mpr (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))

theorem sourceAngleInterval_volume (i : SourceCoordinate) :
    volume (sourceAngleInterval i) = ENNReal.ofReal (sourceAngleUnit i) := by
  simp [sourceAngleInterval, Real.volume_Icc, show 2 * sourceAngleUnit i - sourceAngleUnit i = sourceAngleUnit i by ring]

instance sourceAngleMarginal_probability (i : SourceCoordinate) :
    IsProbabilityMeasure (sourceAngleMarginal i) := by
  unfold sourceAngleMarginal
  apply cond_isProbabilityMeasure_of_finite
  · rw [sourceAngleInterval_volume]; exact (ENNReal.ofReal_pos.mpr (sourceAngleUnit_pos i)).ne'
  · rw [sourceAngleInterval_volume]; exact ENNReal.ofReal_ne_top

instance sourceAngleLaw_probability : IsProbabilityMeasure sourceAngleLaw := by
  unfold sourceAngleLaw
  infer_instance

theorem sourceAngleLaw_coordinate (i : SourceCoordinate) :
    sourceAngleLaw.map (fun θ => θ i) = sourceAngleMarginal i :=
  Measure.infinitePi_map_eval _ _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_PeriodizedUniform
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem sourceFract_measurable : Measurable (Int.fract : ℝ → ℝ) := by
  have hh := sourceCircleRepresentative_measurable.comp sourceCircle_mk_preserving.measurable
  simpa only [Function.comp_def, sourceCircleRepresentative_coe] using hh

/-- Every translated interval of length one maps to the same representative
Haar measure under fractional part. -/
theorem fract_unit_interval (a : ℝ) :
    (volume.restrict (Set.Ioc a (a+1))).map Int.fract = unitIntervalMeasure := by
  have hh := sourceCircleRepresentative_preserving.comp (AddCircle.measurePreserving_mk 1 a)
  have he : sourceCircleRepresentative ∘ ((↑) : ℝ → AddCircle (1 : ℝ)) = Int.fract := by
    funext x
    exact sourceCircleRepresentative_coe x
  simpa only [he] using hh.map_eq

theorem fract_integer_interval (a : ℝ) (n : ℕ) :
    (volume.restrict (Set.Ioc a (a+n))).map Int.fract = (n : ℝ≥0∞) • unitIntervalMeasure := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : Set.Ioc a (a+((n+1 : ℕ) : ℝ)) =
        Set.Ioc a (a+n) ∪ Set.Ioc (a+n) (a+n+1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)]
      congr 1
      push_cast
      ring
    rw [hu, Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add, ih, fract_unit_interval]
    · simp [add_smul]
    · exact sourceFract_measurable

/-- Periodizing normalized interval measure has density at most 1+1/length.
The bound is expressed as domination of measures on every measurable set. -/
theorem fract_interval_domination (a b : ℝ) (hab : a < b) :
    (cond volume (Set.Ioc a b)).map Int.fract ≤
      ENNReal.ofReal (1+1/(b-a)) • unitIntervalMeasure := by
  let n : ℕ := Nat.ceil (b-a)
  have hsub : Set.Ioc a b ⊆ Set.Ioc a (a+n) := by
    apply Set.Ioc_subset_Ioc le_rfl
    have hh : b-a ≤ (n : ℝ) := Nat.le_ceil _
    linarith
  have hle : (volume.restrict (Set.Ioc a b)).map Int.fract ≤
      (n : ℝ≥0∞) • unitIntervalMeasure := by
    rw [← fract_integer_interval a n]
    exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) sourceFract_measurable
  have hscalar : (ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞) ≤
      ENNReal.ofReal (1+1/(b-a)) := by
    have hpos : 0 < b-a := sub_pos.mpr hab
    have hn : (n : ℝ) < b-a+1 := Nat.ceil_lt_add_one hpos.le
    have hreal : (b-a)⁻¹ * (n : ℝ) ≤ 1+1/(b-a) := by
      apply (mul_le_mul_of_nonneg_left hn.le (inv_nonneg.mpr hpos.le)).trans_eq
      field_simp
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Real.volume_Ioc]
  calc
    _ ≤ (ENNReal.ofReal (b-a))⁻¹ • ((n : ℝ≥0∞) • unitIntervalMeasure) := by gcongr
    _ = ((ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞)) • unitIntervalMeasure := smul_smul _ _ _
    _ ≤ _ := by gcongr

/-- Positive scaling carries normalized interval measure to the normalized
scaled interval; this identifies the actual phase law before periodization. -/
theorem cond_interval_mul_pos (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    (cond volume (Set.Ioc a b)).map (fun t => c*t) =
      cond volume (Set.Ioc (c*a) (c*b)) := by
  have hp : (fun t : ℝ => c*t) ⁻¹' Set.Ioc (c*a) (c*b) = Set.Ioc a b := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioc, mul_lt_mul_iff_right₀ hc, mul_le_mul_iff_right₀ hc]
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hclen : 0 < c*b-c*a := by nlinarith
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Real.volume_Ioc, Real.volume_Ioc, ← hp,
    ← Measure.restrict_map (f := fun t : ℝ => c*t) (by fun_prop) measurableSet_Ioc,
    Real.map_volume_mul_left hc.ne', Measure.restrict_smul, smul_smul]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hc), ← ENNReal.ofReal_inv_of_pos hlen,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hlen.le), ← ENNReal.ofReal_inv_of_pos hclen]
  congr 1
  field_simp

theorem cond_closed_interval_eq (a b : ℝ) :
    cond volume (Set.Icc a b) = cond volume (Set.Ioc a b) := by
  unfold ProbabilityTheory.cond
  rw [Real.volume_Icc, Real.volume_Ioc, ← restrict_Ioc_eq_restrict_Icc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Powers
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Finset Filter
open scoped Topology
noncomputable section

theorem sourceSamplingPowers_spec (s : ℕ) (hs : 200000 ≤ sourceBlockSize s) :
    (∀ n ∈ sourceSamplingPowers s,
      samplingQ (sourceBlockSize s)/2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ samplingQ (sourceBlockSize s) ∧ 0 < n) ∧
    (sourceBlockSize s : ℝ)^((69/100 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      ((sourceSamplingPowers s).card : ℝ) ∧
    ((sourceSamplingPowers s : Finset ℤ) : Set ℤ).Pairwise (fun n n' =>
      ¬SamplingConflict (samplingH (sourceBlockSize s))
        (samplingR (sourceBlockSize s) (sourceStageState s).K) n n') := by
  unfold sourceSamplingPowers
  rw [dite_eq_left hs]
  exact Classical.choose_spec (exists_source_sampling_powers _ _ hs (sourceStage s).m_ge_K)

theorem sourceSamplingPowers_eventually : ∀ᶠ s in atTop,
    (∀ n ∈ sourceSamplingPowers s,
      samplingQ (sourceBlockSize s)/2 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ samplingQ (sourceBlockSize s) ∧ 0 < n) ∧
    (sourceBlockSize s : ℝ)^((69/100 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      ((sourceSamplingPowers s).card : ℝ) ∧
    ((sourceSamplingPowers s : Finset ℤ) : Set ℤ).Pairwise (fun n n' =>
      ¬SamplingConflict (samplingH (sourceBlockSize s))
        (samplingR (sourceBlockSize s) (sourceStageState s).K) n n') := by
  filter_upwards [sourceBlockSize_tendsto.eventually (eventually_ge_atTop 200000)] with s hs
  exact sourceSamplingPowers_spec s hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Fourier
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceBlockSize_monotone : Monotone sourceBlockSize := by
  apply monotone_nat_of_le_succ
  intro s
  have hp := (sourceStage (s+1)).previous_size
  have hd : (sourceBlockSize s : ℝ) ≤ (sourceStageState (s+1)).d := by
    change (sourceBlockSize s : ℝ) ≤ ((sourceStageState s).d+(sourceStage s).m : ℕ)
    change ((sourceStage s).m : ℝ) ≤ ((sourceStageState s).d+(sourceStage s).m : ℕ)
    push_cast
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hm : (sourceBlockSize s : ℝ) ≤ sourceBlockSize (s+1) := by
    change ((sourceStageState (s+1)).d : ℝ) ≤ (sourceBlockSize (s+1) : ℝ)/100 at hp
    have := Nat.cast_nonneg (α := ℝ) (sourceBlockSize (s+1))
    linarith
  exact_mod_cast hm

theorem sourceFrequencyScale_monotone :
    Monotone (fun s => sourceBlockSize s * (sourceStageState s).K) := by
  have hK : Monotone (fun s => (sourceStageState s).K) := by
    apply monotone_nat_of_le_succ
    intro s
    have := sourceStage_cutoff_growth s
    omega
  intro s t hst
  exact Nat.mul_le_mul (sourceBlockSize_monotone hst) (hK hst)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Periodization
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Lower counterpart to periodized interval domination; the floor-length
subinterval contributes exact Haar measure. -/
theorem fract_interval_lower (a b : ℝ) (hab : a < b) :
    ENNReal.ofReal (1-1/(b-a)) • unitIntervalMeasure ≤
      (cond volume (Set.Ioc a b)).map Int.fract := by
  let n : ℕ := Nat.floor (b-a)
  have hpos : 0 < b-a := sub_pos.mpr hab
  have hsub : Set.Ioc a (a+n) ⊆ Set.Ioc a b := by
    apply Set.Ioc_subset_Ioc le_rfl
    have hh : (n : ℝ) ≤ b-a := Nat.floor_le hpos.le
    linarith
  have hle : (n : ℝ≥0∞) • unitIntervalMeasure ≤
      (volume.restrict (Set.Ioc a b)).map Int.fract := by
    rw [← fract_integer_interval a n]
    exact Measure.map_mono (Measure.restrict_mono hsub le_rfl) sourceFract_measurable
  have hscalar : ENNReal.ofReal (1-1/(b-a)) ≤
      (ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞) := by
    have hn : b-a < (n : ℝ)+1 := Nat.lt_floor_add_one (b-a)
    have hreal : 1-1/(b-a) ≤ (b-a)⁻¹ * (n : ℝ) := by
      apply (le_inv_mul_iff₀ hpos).mpr
      field_simp
      linarith
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    exact ENNReal.ofReal_le_ofReal hreal
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Real.volume_Ioc]
  calc
    _ ≤ ((ENNReal.ofReal (b-a))⁻¹ * (n : ℝ≥0∞)) • unitIntervalMeasure := by gcongr
    _ = (ENNReal.ofReal (b-a))⁻¹ • ((n : ℝ≥0∞) • unitIntervalMeasure) :=
      (smul_smul _ _ _).symm
    _ ≤ _ := by gcongr

/-- Two-sided near-uniformity for the actual single-phase law, on every
Borel set. The error is exactly 1/(n times the source interval length). -/
theorem sourceAngle_phase_sandwich (i : SourceCoordinate) (n : ℝ) (hn : 0 < n) :
    ENNReal.ofReal (1-1/(n*sourceAngleUnit i)) • unitIntervalMeasure ≤
      (sourceAngleMarginal i).map (fun t => Int.fract (n*t)) ∧
    (sourceAngleMarginal i).map (fun t => Int.fract (n*t)) ≤
      ENNReal.ofReal (1+1/(n*sourceAngleUnit i)) • unitIntervalMeasure := by
  have ha := sourceAngleUnit_pos i
  have he : (sourceAngleMarginal i).map (fun t => Int.fract (n*t)) =
      (cond volume (Set.Ioc (n*sourceAngleUnit i) (n*(2*sourceAngleUnit i)))).map Int.fract := by
    rw [← cond_interval_mul_pos (sourceAngleUnit i) (2*sourceAngleUnit i) n (by linarith) hn,
      Measure.map_map sourceFract_measurable (by fun_prop)]
    rw [sourceAngleMarginal, sourceAngleInterval, cond_closed_interval_eq]
    rfl
  rw [he]
  have hpos : n*sourceAngleUnit i < n*(2*sourceAngleUnit i) := by nlinarith
  have hlen : n*(2*sourceAngleUnit i)-n*sourceAngleUnit i = n*sourceAngleUnit i := by ring
  constructor
  · simpa only [hlen] using fract_interval_lower _ _ hpos
  · simpa only [hlen] using fract_interval_domination _ _ hpos

/-- Nonnegative tests inherit the exact relative error from a measure sandwich. -/
theorem integral_error_of_measure_sandwich {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hlo : ENNReal.ofReal (1-ε) • μ ≤ ν)
    (hhi : ν ≤ ENNReal.ofReal (1+ε) • μ)
    (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g μ) :
    Integrable g ν ∧ |(∫ x, g x ∂ν) - ∫ x, g x ∂μ| ≤ ε * ∫ x, g x ∂μ := by
  have hgui := hgi.smul_measure (c := ENNReal.ofReal (1+ε)) ENNReal.ofReal_ne_top
  have hgν := hgui.mono_measure hhi
  refine ⟨hgν, ?_⟩
  have hl := integral_mono_measure hlo (Filter.Eventually.of_forall hg) hgν
  have hu := integral_mono_measure hhi (Filter.Eventually.of_forall hg) hgui
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hl
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hu
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The source's single-phase test estimate for all integrable nonnegative
weights, not merely for rectangle indicators. -/
theorem sourceAngle_single_phase_test (i : SourceCoordinate) (n : ℝ) (hn : 0 < n)
    (hlen : 1 ≤ n*sourceAngleUnit i) (g : ℝ → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hgm : Measurable g) (hgi : Integrable g unitIntervalMeasure) :
    |(∫ t, g (Int.fract (n*t)) ∂sourceAngleMarginal i) -
        ∫ t, g t ∂unitIntervalMeasure| ≤
      (1/(n*sourceAngleUnit i)) * ∫ t, g t ∂unitIntervalMeasure := by
  have hp := sourceAngle_phase_sandwich i n hn
  have he0 : 0 ≤ 1/(n*sourceAngleUnit i) := by positivity
  have he1 : 1/(n*sourceAngleUnit i) ≤ 1 := by
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlen).trans_eq (by norm_num)
  have hh := (integral_error_of_measure_sandwich unitIntervalMeasure _ _ he0 he1 hp.1 hp.2 g hg hgi).2
  have hphase : Measurable (fun t : ℝ => Int.fract (n*t)) :=
    sourceFract_measurable.comp (measurable_const.mul measurable_id)
  rw [integral_map hphase.aemeasurable hgm.aestronglyMeasurable] at hh
  exact hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Discrepancy
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal Topology
noncomputable section

/-- Every constructed power is long enough for density at most two on
every coordinate in the sampling prefix. -/
theorem sourceSampling_phase_length (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    1 ≤ (n : ℝ)*sourceAngleUnit i := by
  have hm : (200000 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast hs
  have hm0 := sourceBlockSize_pos s
  have hspec := (sourceSamplingPowers_spec s hs).1 n hn
  have hQ : (sourceBlockSize s : ℝ)^3 ≤ samplingQ (sourceBlockSize s) := by
    unfold samplingQ
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hN : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤ (sourceBlockSize s : ℝ)^2 := by
    have hh : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤
        (sourceBlockSize s : ℝ)*(sourceStageState s).K := by exact_mod_cast sourceFrequencyScale_monotone hi
    have hK : ((sourceStageState s).K : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_K
    nlinarith
  have hnp : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤ (n : ℝ) := by
    nlinarith [hspec.1,sq_nonneg (sourceBlockSize s : ℝ)]
  unfold sourceAngleUnit
  rw [mul_one_div,le_div_iff₀ (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)),one_mul]
  exact hnp

theorem sourceSampling_phase_domination (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    sourceAngleLaw.map (fun θ => Int.fract ((n : ℝ)*θ i)) ≤
      (2 : ℝ≥0∞) • unitIntervalMeasure := by
  have hp : Measurable (fun t : ℝ => Int.fract ((n : ℝ)*t)) :=
    sourceFract_measurable.comp (measurable_const.mul measurable_id)
  have he : sourceAngleLaw.map (fun θ => Int.fract ((n : ℝ)*θ i)) =
      (sourceAngleMarginal i).map (fun t => Int.fract ((n : ℝ)*t)) := by
    rw [← sourceAngleLaw_coordinate i,Measure.map_map hp (measurable_pi_apply i)]
    rfl
  rw [he]
  have hnp : (0 : ℝ) < n := by exact_mod_cast ((sourceSamplingPowers_spec s hs).1 n hn).2.2
  have hh := (sourceAngle_phase_sandwich i (n : ℝ) hnp).2
  apply hh.trans
  have hlen := sourceSampling_phase_length s hs i hi n hn
  have hiR : 1/(n*sourceAngleUnit i) ≤ (1 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hlen
  have heps : ENNReal.ofReal (1+1/(n*sourceAngleUnit i)) ≤ (2 : ℝ≥0∞) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show 1+1/(n*sourceAngleUnit i) ≤ (2 : ℝ) by linarith)
  gcongr

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Weights
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

theorem samplingWeight_measurable (triangular : Bool) (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingWeight triangular h α p.1 p.2) := by
  cases triangular <;> unfold samplingWeight samplingDistance <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Measurable.ite _ (by fun_prop) measurable_const
    exact (measurableSet_le measurable_const (measurable_fst.min (measurable_const.sub measurable_fst))).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul (measurable_fst.min (measurable_const.sub measurable_fst)))))
  · exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst))) measurable_const measurable_const

theorem samplingWeight_support (triangular : Bool) (h α s t : ℝ)
    (_hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (_hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    0 < t ∧ t < 1-s := by
  cases triangular
  · unfold samplingWeight at hw
    simp only [Bool.false_eq_true,ite_false] at hw
    split_ifs at hw with hc
    · have hd : 0 < samplingDistance s := hα.trans_le hc.1
      have hd1 : samplingDistance s ≤ 1-s := min_le_right _ _
      exact ⟨hc.2.1, hc.2.2.trans_le ((by simpa using
        (mul_lt_mul_of_pos_right hh1 hd).le : h * samplingDistance s ≤ samplingDistance s).trans hd1)⟩
    · exact False.elim (hw rfl)
  · simpa only [samplingWeight,ite_true,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hw

/-- The positive weight already orders each prefix coordinate strictly,
with no wrap of the orbit endpoint. -/
theorem samplingWeight_orders (triangular : Bool) (h α s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    Int.fract (s+t) = s+t ∧ s < Int.fract (s+t) := by
  have ht := samplingWeight_support triangular h α s t hh hh1 hα hs hw
  have he := Int.fract_eq_self.mpr (show s+t ∈ Set.Ico (0 : ℝ) 1 from ⟨by linarith [hs.1],by linarith⟩)
  exact ⟨he,by rw [he]; linarith⟩

/-- Exact first marginal of either untested one-coordinate weight. -/
theorem samplingWeight_first_integral (triangular : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    (∫ t, samplingWeight triangular h α s t ∂unitIntervalMeasure) =
      if triangular then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have hvol (L : ℝ) (hL : 0 ≤ L) (hL1 : L ≤ 1) :
      unitIntervalMeasure (Set.Ioo (0 : ℝ) L) = ENNReal.ofReal L := by
    unfold unitIntervalMeasure
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr (by
      intro t ht; exact ⟨ht.1.le,ht.2.trans_le hL1⟩),Real.volume_Ioo,sub_zero]
  cases triangular
  · simp only [Bool.false_eq_true,ite_false]
    by_cases hc : α ≤ samplingDistance s
    · have hd : 0 < samplingDistance s := hα.trans_le hc
      have hL : 0 < h*samplingDistance s := mul_pos hh hd
      have hL1 : h*samplingDistance s ≤ 1 := by
        have := min_le_right s (1-s)
        change samplingDistance s ≤ 1-s at this
        nlinarith [hs.1]
      have he : samplingWeight false h α s =
          (Set.Ioo 0 (h*samplingDistance s)).indicator (fun _ => 1/(h*samplingDistance s)) := by
        funext t
        simp [samplingWeight,hc,Set.indicator,Set.mem_Ioo]
      rw [he,integral_indicator measurableSet_Ioo]
      simp [hc,hvol (h*samplingDistance s) hL.le hL1,ENNReal.toReal_ofReal hL.le,measureReal_def]
      field_simp
    · have he : samplingWeight false h α s = fun _ => 0 := by funext t; simp [samplingWeight,hc]
      simp [he,hc]
  · simp only [ite_true]
    have he : samplingWeight true h α s = (Set.Ioo 0 (1-s)).indicator (fun _ => (1 : ℝ)) := by
      funext t
      simp [samplingWeight,Set.indicator,Set.mem_Ioo]
    rw [he,integral_indicator measurableSet_Ioo]
    simp [hvol (1-s) (by linarith [hs.2]) (by linarith [hs.1]),ENNReal.toReal_ofReal,show 0 ≤ 1-s by linarith [hs.2],measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Transport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem unitInterval_split (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitIntervalMeasure = volume.restrict (Set.Ioc (0 : ℝ) c) + volume.restrict (Set.Ioc c 1) := by
  unfold unitIntervalMeasure
  rw [restrict_Ico_eq_restrict_Ioc,← Set.Ioc_union_Ioc_eq_Ioc hc hc1,
    Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]

theorem map_interval_affine (a b c d : ℝ) (hc : 0 < c) :
    (volume.restrict (Set.Ioc a b)).map (fun x => c*x+d) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Set.Ioc (c*a+d) (c*b+d)) := by
  have hp : (fun x : ℝ => c*x+d) ⁻¹' Set.Ioc (c*a+d) (c*b+d) = Set.Ioc a b := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Ioc,add_lt_add_iff_right,add_le_add_iff_right,
      mul_lt_mul_iff_right₀ hc,mul_le_mul_iff_right₀ hc]
  have hmap : volume.map (fun x : ℝ => c*x+d) = ENNReal.ofReal c⁻¹ • volume := by
    have he : (fun x : ℝ => c*x+d) = (fun x : ℝ => x+d) ∘ (fun x : ℝ => c*x) := rfl
    rw [he,← Measure.map_map (by fun_prop) (by fun_prop),Real.map_volume_mul_left hc.ne',
      Measure.map_smul,
      (measurePreserving_add_right (volume : Measure ℝ) d).map_eq,abs_of_pos (inv_pos.mpr hc)]
  rw [← hp,← Measure.restrict_map (f := fun x : ℝ => c*x+d) (by fun_prop) measurableSet_Ioc,
    hmap,Measure.restrict_smul]

theorem samplingTransportDensity_measurable :
    Measurable (fun p : ℝ × ℝ => samplingTransportDensity p.1 p.2) := by
  unfold samplingTransportDensity
  exact Measurable.ite (measurableSet_le measurable_snd ((measurable_const.add measurable_fst).div_const 2))
    (by fun_prop) (by fun_prop)

/-- This is the actual push-forward density, not an assumed ideal moment. -/
theorem samplingTransport_density (v : ℝ) (hv : 0 ≤ v) (hv1 : v < 1) :
    unitIntervalMeasure.map (samplingTransport v) =
      unitIntervalMeasure.withDensity (fun s => ENNReal.ofReal (samplingTransportDensity v s)) := by
  let c := (1+v)/2
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hleft : (volume.restrict (Set.Ioc (0 : ℝ) (1/2))).map (samplingTransport v) =
      ENNReal.ofReal (1/(1+v)) • volume.restrict (Set.Ioc (0 : ℝ) c) := by
    have he : samplingTransport v =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (1/2))] (fun z => (1+v)*z+0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      unfold samplingTransport samplingDistance
      rw [min_eq_left (by linarith [hz.2])]
      ring
    rw [Measure.map_congr he,map_interval_affine _ _ _ _ (by linarith)]
    simp only [mul_zero,add_zero,one_div]
    congr 3
  have hright : (volume.restrict (Set.Ioc (1/2 : ℝ) 1)).map (samplingTransport v) =
      ENNReal.ofReal (1/(1-v)) • volume.restrict (Set.Ioc c (1 : ℝ)) := by
    have he : samplingTransport v =ᵐ[volume.restrict (Set.Ioc (1/2 : ℝ) 1)] (fun z => (1-v)*z+v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      unfold samplingTransport samplingDistance
      rw [min_eq_right (by linarith [hz.1])]
      ring
    rw [Measure.map_congr he,map_interval_affine _ _ _ _ (by linarith)]
    have hc' : (1-v)*(1/2)+v = c := by dsimp [c]; ring
    rw [hc',show (1-v)*1+v = 1 by ring]
    simp [one_div]
  have hdleft : (volume.restrict (Set.Ioc (0 : ℝ) c)).withDensity
      (fun s => ENNReal.ofReal (samplingTransportDensity v s)) =
      ENNReal.ofReal (1/(1+v)) • volume.restrict (Set.Ioc (0 : ℝ) c) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp [samplingTransportDensity,show z ≤ (1+v)/2 from hz.2]
  have hdright : (volume.restrict (Set.Ioc c (1 : ℝ))).withDensity
      (fun s => ENNReal.ofReal (samplingTransportDensity v s)) =
      ENNReal.ofReal (1/(1-v)) • volume.restrict (Set.Ioc c (1 : ℝ)) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp [samplingTransportDensity,show ¬z ≤ (1+v)/2 from not_le.mpr hz.1]
  conv_lhs => rw [unitInterval_split (1/2) (by norm_num) (by norm_num)]
  have htm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
  rw [Measure.map_add _ _ htm,hleft,hright]
  conv_rhs => rw [unitInterval_split c hc hc1]
  rw [withDensity_add_measure,hdleft,hdright]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingTransportDensity_bounds (h v s : ℝ) (hh : 0 ≤ h) (hh1 : h < 1)
    (hv : 0 ≤ v) (hvh : v ≤ h) :
    0 ≤ samplingTransportDensity v s ∧ samplingTransportDensity v s ≤ 1/(1-h) ∧
      |samplingTransportDensity v s-1| ≤ h/(1-h) := by
  have hmh : 0 < 1-h := by linarith
  have hph : 0 < 1+h := by linarith
  have hmv : 0 < 1-v := by linarith
  have hpv : 0 < 1+v := by linarith
  have hlo : 1/(1+h) ≤ samplingTransportDensity v s := by
    unfold samplingTransportDensity
    split_ifs
    · exact one_div_le_one_div_of_le hpv (by linarith)
    · exact one_div_le_one_div_of_le hmv (by linarith)
  have hhi : samplingTransportDensity v s ≤ 1/(1-h) := by
    unfold samplingTransportDensity
    split_ifs <;> exact one_div_le_one_div_of_le hmh (by linarith)
  have hl : 1-h/(1-h) ≤ 1/(1+h) := by
    field_simp
    nlinarith
  have hr : 1/(1-h)-1 = h/(1-h) := by field_simp; ring
  exact ⟨(by positivity : 0 ≤ 1/(1+h)).trans hlo,hhi,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem samplingTransportDensity_integral (v : ℝ) (hv : 0 ≤ v) (hv1 : v < 1) :
    (∫ s, samplingTransportDensity v s ∂unitIntervalMeasure) = 1 := by
  have hm : Measurable (samplingTransportDensity v) :=
    samplingTransportDensity_measurable.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (samplingTransportDensity v) unitIntervalMeasure :=
    (integrable_const (1/(1-v))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1]
        exact (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).2.1))
  have hmap := congrArg (fun μ : Measure ℝ => μ Set.univ) (samplingTransport_density v hv hv1)
  have htm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
  rw [Measure.map_apply htm MeasurableSet.univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hmap
  simp only [Set.preimage_univ,measure_univ] at hmap
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun s => (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1))
  rw [← hmap] at he
  have hn : 0 ≤ ∫ s, samplingTransportDensity v s ∂unitIntervalMeasure := integral_nonneg (fun s => (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1)
  have hh := congrArg ENNReal.toReal he
  simpa [ENNReal.toReal_ofReal hn] using hh

theorem samplingVelocity_probability (h : ℝ) (hh : 0 < h) : IsProbabilityMeasure (samplingVelocityMeasure h) := by
  apply cond_isProbabilityMeasure_of_finite
  · simp [Real.volume_Ioc,hh]
  · simp [Real.volume_Ioc]

theorem samplingIdealSecond_bounds (h s : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    0 ≤ samplingIdealSecond h s ∧ samplingIdealSecond h s ≤ 1/(1-h) ∧
      |samplingIdealSecond h s-1| ≤ h/(1-h) := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hm : Measurable (fun v => samplingTransportDensity v s) :=
    samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun v => samplingTransportDensity v s) (samplingVelocityMeasure h) :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (by
      filter_upwards [hv] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1]
      exact (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1)
  have hnon : 0 ≤ samplingIdealSecond h s := integral_nonneg_of_ae (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1))
  have hu := integral_mono_ae hqi (integrable_const (1/(1-h))) (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1))
  refine ⟨hnon,by simpa [samplingIdealSecond] using hu,?_⟩
  have he : samplingIdealSecond h s-1 = ∫ v, samplingTransportDensity v s-1 ∂samplingVelocityMeasure h := by
    rw [integral_sub hqi (integrable_const 1)]
    simp [samplingIdealSecond]
  rw [he]
  calc
    _ ≤ ∫ v, |samplingTransportDensity v s-1| ∂samplingVelocityMeasure h := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v => samplingTransportDensity v s-1)
    _ ≤ ∫ _v, h/(1-h) ∂samplingVelocityMeasure h := by
      apply integral_mono_ae
      · simpa [Real.norm_eq_abs] using (hqi.sub (integrable_const 1)).norm
      · exact integrable_const _
      · exact hv.mono (fun v hv => (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.2)
    _ = _ := by simp

theorem samplingIdealSecond_measurable (h : ℝ) (hh : 0 < h) : Measurable (samplingIdealSecond h) := by
  have := samplingVelocity_probability h hh
  exact samplingTransportDensity_measurable.stronglyMeasurable.integral_prod_left.measurable

/-- Fubini gives the exact mass identity for the averaged transport density. -/
theorem samplingIdealSecond_integral (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ s, samplingIdealSecond h s ∂unitIntervalMeasure) = 1 := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hvp : ∀ᵐ p : ℝ × ℝ ∂(samplingVelocityMeasure h).prod unitIntervalMeasure,
      p.1 ∈ Set.Ioc (0 : ℝ) h := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    exact hv.mono (fun v hv => Eventually.of_forall (fun _ => hv))
  have hqi : Integrable (fun p : ℝ × ℝ => samplingTransportDensity p.1 p.2)
      ((samplingVelocityMeasure h).prod unitIntervalMeasure) :=
    (integrable_const (1/(1-h))).mono' samplingTransportDensity_measurable.aestronglyMeasurable (by
      filter_upwards [hvp] with p hp
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h p.1 p.2 hh.le hh1 hp.1.le hp.2).1]
      exact (samplingTransportDensity_bounds h p.1 p.2 hh.le hh1 hp.1.le hp.2).2.1)
  have hswap := integral_integral_swap (f := fun v s => samplingTransportDensity v s) hqi
  calc
    _ = ∫ v, (∫ s, samplingTransportDensity v s ∂unitIntervalMeasure) ∂samplingVelocityMeasure h := hswap.symm
    _ = ∫ _v, (1 : ℝ) ∂samplingVelocityMeasure h := integral_congr_ae
      (hv.mono (fun v hv => samplingTransportDensity_integral v hv.1.le (hv.2.trans_lt hh1)))
    _ = 1 := by simp

/-- The source's quadratic cancellation for the actual averaged uncut
transport density. The exact mass-one identity eliminates the linear term. -/
theorem samplingIdealSecond_square (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ s, samplingIdealSecond h s^2 ∂unitIntervalMeasure) =
      1+(∫ s, (samplingIdealSecond h s-1)^2 ∂unitIntervalMeasure) ∧
    (∫ s, samplingIdealSecond h s^2 ∂unitIntervalMeasure) ≤ 1+h^2/(1-h)^2 := by
  let q := samplingIdealSecond h
  let C := h/(1-h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm := samplingIdealSecond_measurable h hh
  have hqi : Integrable q unitIntervalMeasure :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingIdealSecond_bounds h s hh hh1).1]
      exact (samplingIdealSecond_bounds h s hh hh1).2.1))
  have hdev (s : ℝ) : (q s-1)^2 ≤ C^2 := by
    have hb := abs_le.mp (samplingIdealSecond_bounds h s hh hh1).2.2
    dsimp [C,q]
    nlinarith
  have hdi : Integrable (fun s => (q s-1)^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (by fun_prop) (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hdev s))
  have heq : (fun s => q s^2) = (fun s => ((q s-1)^2+2*q s)-1) := by funext s; ring
  have hmass : (∫ s, q s ∂unitIntervalMeasure) = 1 := samplingIdealSecond_integral h hh hh1
  have he : (∫ s, q s^2 ∂unitIntervalMeasure) = 1+∫ s, (q s-1)^2 ∂unitIntervalMeasure := by
    rw [heq]
    have hsum : Integrable (fun s => (q s-1)^2+2*q s) unitIntervalMeasure := hdi.add (hqi.const_mul 2)
    rw [integral_sub hsum (integrable_const 1),integral_add hdi (hqi.const_mul 2),integral_const_mul,hmass]
    simp
    ring
  refine ⟨he,?_⟩
  have hu := integral_mono_ae hdi (integrable_const (C^2)) (Eventually.of_forall hdev)
  simp at hu
  have hCeq : C^2 = h^2/(1-h)^2 := by dsimp [C]; rw [div_pow]
  rw [he]
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_WeightTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- At each retained starting coordinate, the source weight is exactly the
law of the displacement v times the distance to the endpoint. -/
theorem samplingWeight_displacement (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance z) :
    unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (samplingWeight false h α z t)) =
      (samplingVelocityMeasure h).map (fun v => samplingDistance z * v) := by
  let d := samplingDistance z
  have hd : 0 < d := hα.trans_le hcut
  have hL : 0 < h*d := mul_pos hh hd
  have hd1 : d ≤ 1-z := min_le_right _ _
  have hL1 : h*d ≤ 1 := by nlinarith [hz.1]
  have he : (fun t => ENNReal.ofReal (samplingWeight false h α z t)) =
      (Set.Ioo 0 (h*d)).indicator (fun _ => ENNReal.ofReal (1/(h*d))) := by
    funext t
    simp only [samplingWeight,Bool.false_eq_true,ite_false,hcut,true_and,Set.indicator,Set.mem_Ioo,d]
    split_ifs <;> simp
  rw [he,withDensity_indicator measurableSet_Ioo,withDensity_const]
  unfold unitIntervalMeasure
  rw [Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.mpr (show Set.Ioo 0 (h*d) ⊆ Set.Ico (0 : ℝ) 1 from
      fun t ht => ⟨ht.1.le,ht.2.trans_le hL1⟩),restrict_Ioo_eq_restrict_Ioc]
  unfold samplingVelocityMeasure ProbabilityTheory.cond
  rw [Measure.map_smul]
  have ha := map_interval_affine 0 h d 0 hd
  simp only [mul_zero,add_zero] at ha
  rw [ha,smul_smul,Real.volume_Ioc,sub_zero]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos hh,← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
  congr 1
  dsimp [d]
  field_simp
  simp [mul_comm]

/-- Exact substitution t=v*Delta(z), at each retained starting point. -/
theorem samplingWeight_transport_integral (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance z)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t) ∂unitIntervalMeasure) =
      ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h := by
  have hw : Measurable (fun t => ENNReal.ofReal (samplingWeight false h α z t)) :=
    ((samplingWeight_measurable false h α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hFz : Measurable (fun t => F (z+t)) := hF.comp (by fun_prop)
  have hi := lintegral_withDensity_eq_lintegral_mul unitIntervalMeasure hw hFz
  simp only [Pi.mul_apply] at hi
  rw [← hi,
    samplingWeight_displacement h α z hh hh1 hα hz hcut,
    lintegral_map hFz (by fun_prop)]
  apply lintegral_congr
  intro v
  simp [samplingTransport,mul_comm]

/-- Discarding the cutoff only increases the weighted endpoint law. -/
theorem samplingWeight_transport_le (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t) ∂unitIntervalMeasure) ≤
      ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h := by
  by_cases hc : α ≤ samplingDistance z
  · exact (samplingWeight_transport_integral h α z hh hh1 hα hz hc F hF).le
  · simp [samplingWeight,hc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_AveragedTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- ENNReal form of the constructed averaged density. -/
theorem samplingIdealSecond_lintegral (h s : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    ENNReal.ofReal (samplingIdealSecond h s) =
      ∫⁻ v, ENNReal.ofReal (samplingTransportDensity v s) ∂samplingVelocityMeasure h := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hm : Measurable (fun v => samplingTransportDensity v s) :=
    samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun v => samplingTransportDensity v s) (samplingVelocityMeasure h) :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (by
      filter_upwards [hv] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1]
      exact (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1)
  exact ofReal_integral_eq_lintegral_ofReal hqi (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1))

/-- The average of the actual transport laws has density q_h. -/
theorem samplingTransport_average (h : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h ∂unitIntervalMeasure) =
      ∫⁻ s, ENNReal.ofReal (samplingIdealSecond h s)*F s ∂unitIntervalMeasure := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have htm : Measurable (fun p : ℝ × ℝ => samplingTransport p.2 p.1) := by
    unfold samplingTransport samplingDistance
    fun_prop
  have hswap := lintegral_lintegral_swap (μ := unitIntervalMeasure) (ν := samplingVelocityMeasure h) (f := fun z v => F (samplingTransport v z)) (hF.comp htm).aemeasurable
  rw [hswap]
  calc
    _ = ∫⁻ v, (∫⁻ s, ENNReal.ofReal (samplingTransportDensity v s)*F s ∂unitIntervalMeasure)
        ∂samplingVelocityMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hv] with v hv
      have hm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
      rw [← lintegral_map hF hm,samplingTransport_density v hv.1.le (hv.2.trans_lt hh1)]
      have hmd : Measurable (fun s => ENNReal.ofReal (samplingTransportDensity v s)) :=
        (samplingTransportDensity_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
      exact lintegral_withDensity_eq_lintegral_mul unitIntervalMeasure hmd hF
    _ = ∫⁻ s, (∫⁻ v, ENNReal.ofReal (samplingTransportDensity v s)*F s ∂samplingVelocityMeasure h)
        ∂unitIntervalMeasure := lintegral_lintegral_swap
          (samplingTransportDensity_measurable.ennreal_ofReal.mul (hF.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      have hmd : Measurable (fun v => ENNReal.ofReal (samplingTransportDensity v s)) :=
        (samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
      rw [lintegral_mul_const _ hmd,← samplingIdealSecond_lintegral h s hh hh1]

/-- An actual cutoff-weight endpoint estimate, with no assumed second-marginal
identification. It holds against every measurable nonnegative test. -/
theorem samplingWeight_endpoint_domination (h α : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t)
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
        ∫⁻ s, ENNReal.ofReal (samplingIdealSecond h s)*F s ∂unitIntervalMeasure := by
  rw [← samplingTransport_average h hh hh1 F hF]
  apply lintegral_mono_ae
  filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
    ae_restrict_mem measurableSet_Ico] with z hz
  exact samplingWeight_transport_le h α z hh hh1 hα hz F hF

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondDensity
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingSecondWeight_measurable (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2) :=
  (samplingWeight_measurable false h α).comp
    ((sourceFract_measurable.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)

theorem samplingSecondWeight_integrable (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (samplingSecondWeight h α s) unitIntervalMeasure := by
  have hm : Measurable (samplingSecondWeight h α s) :=
    (samplingSecondWeight_measurable h α).comp (measurable_const.prodMk measurable_id)
  exact (integrable_const (max 1 (1/(h*α)))).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs]
      change |samplingWeight false h α (Int.fract (s-t)) t| ≤ _
      rw [abs_of_nonneg (samplingWeight_bounds false h α (Int.fract (s-t)) t hh hα).1]
      exact (samplingWeight_bounds false h α _ t hh hα).2))

theorem samplingSecondDensity_lintegral (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    ENNReal.ofReal (samplingSecondDensity h α s) =
      ∫⁻ t, ENNReal.ofReal (samplingSecondWeight h α s t) ∂unitIntervalMeasure :=
  ofReal_integral_eq_lintegral_ofReal (samplingSecondWeight_integrable h α s hh hα)
    (Eventually.of_forall (fun t => (samplingWeight_bounds false h α _ t hh hα).1))

theorem samplingSecondDensity_measurable (h α : ℝ) : Measurable (samplingSecondDensity h α) :=
  (samplingSecondWeight_measurable h α).stronglyMeasurable.integral_prod_right.measurable

theorem sampling_fract_inverse (z t : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    Int.fract (Int.fract (z+t)-t) = z := by
  have he : Int.fract (z+t)-t = z-(Int.floor (z+t) : ℝ) := by rw [Int.fract]; ring
  rw [he,Int.fract_sub_intCast,Int.fract_eq_self.mpr hz]

/-- Haar substitution identifies the actual second-oriented integral with
the weighted endpoint law; no marginal-density hypothesis is assumed. -/
theorem samplingSecondDensity_test (h α : ℝ) (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, ENNReal.ofReal (samplingSecondDensity h α s)*F s ∂unitIntervalMeasure) =
      ∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t)
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
  have hwm := samplingSecondWeight_measurable h α
  calc
    _ = ∫⁻ s, ∫⁻ t, ENNReal.ofReal (samplingSecondWeight h α s t)*F s
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_congr
      intro s
      have hmd : Measurable (fun t => ENNReal.ofReal (samplingSecondWeight h α s t)) :=
        (hwm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
      rw [samplingSecondDensity_lintegral h α s hh hα,lintegral_mul_const _ hmd]
    _ = ∫⁻ t, ∫⁻ s, ENNReal.ofReal (samplingSecondWeight h α s t)*F s
        ∂unitIntervalMeasure ∂unitIntervalMeasure :=
      lintegral_lintegral_swap (hwm.ennreal_ofReal.mul (hF.comp measurable_fst)).aemeasurable
    _ = ∫⁻ t, ∫⁻ z, ENNReal.ofReal (samplingWeight false h α z t)*F (Int.fract (z+t))
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_congr
      intro t
      have hm : Measurable (fun s => ENNReal.ofReal (samplingSecondWeight h α s t)*F s) :=
        ((hwm.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul hF
      rw [← (unitInterval_rotate_preserving t).lintegral_comp hm]
      apply lintegral_congr_ae
      filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with z hz
      simp only [samplingSecondWeight,sampling_fract_inverse z t hz]
    _ = ∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (Int.fract (z+t))
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_lintegral_swap
      exact (((samplingWeight_measurable false h α).comp measurable_swap).ennreal_ofReal.mul
        (hF.comp (sourceFract_measurable.comp (measurable_snd.add measurable_fst)))).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with z hz
      apply lintegral_congr
      intro t
      by_cases hw : samplingWeight false h α z t = 0
      · simp [hw]
      · rw [(samplingWeight_orders false h α z t hh hh1 hα hz hw).1]

/-- The actual cutoff second marginal is dominated almost everywhere by
q_h, completing the missing connection to the quadratic ideal moment. -/
theorem samplingSecondDensity_le_ideal (h α : ℝ) (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) :
    ∀ᵐ s ∂unitIntervalMeasure, samplingSecondDensity h α s ≤ samplingIdealSecond h s := by
  have he : ∀ᵐ s ∂unitIntervalMeasure,
      ENNReal.ofReal (samplingSecondDensity h α s) ≤ ENNReal.ofReal (samplingIdealSecond h s) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (samplingSecondDensity_measurable h α).ennreal_ofReal
    intro S hS _
    have hb := samplingWeight_endpoint_domination h α hh hh1 hα (S.indicator (fun _ => 1))
      (measurable_const.indicator hS)
    rw [← samplingSecondDensity_test h α hh hh1 hα _ (measurable_const.indicator hS)] at hb
    have hind (g : ℝ → ℝ≥0∞) : (fun s => g s*S.indicator (fun _ => 1) s) = S.indicator g := by
      funext s
      by_cases hs : s ∈ S <;> simp [Set.indicator,hs]
    rw [hind,hind,lintegral_indicator hS,lintegral_indicator hS] at hb
    exact hb
  filter_upwards [he] with s hs
  exact (ENNReal.ofReal_le_ofReal_iff (samplingIdealSecond_bounds h s hh hh1).1).mp hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedSecondMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingTestedSecondWeight_measurable (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingTestedSecondWeight h α E G p.1 p.2) := by
  unfold samplingTestedSecondWeight
  exact Measurable.ite ((hE.preimage (sourceFract_measurable.comp
    (measurable_fst.sub measurable_snd))).inter (hG.preimage measurable_fst))
    (samplingSecondWeight_measurable h α) measurable_const

theorem samplingTestedSecondWeight_bounds (h α : ℝ) (E G : Set ℝ) (s t : ℝ)
    (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingTestedSecondWeight h α E G s t ∧
      samplingTestedSecondWeight h α E G s t ≤ samplingSecondWeight h α s t := by
  have hn : 0 ≤ samplingSecondWeight h α s t := (samplingWeight_bounds false h α _ t hh hα).1
  unfold samplingTestedSecondWeight
  split_ifs <;> simp [hn]

theorem samplingTestedSecondDensity_measurable (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingTestedSecondDensity h α E G) :=
  (samplingTestedSecondWeight_measurable h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

theorem samplingTestedSecondDensity_bounds (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) (s : ℝ) :
    0 ≤ samplingTestedSecondDensity h α E G s ∧
      samplingTestedSecondDensity h α E G s ≤ samplingSecondDensity h α s := by
  have hm : Measurable (samplingTestedSecondWeight h α E G s) :=
    (samplingTestedSecondWeight_measurable h α E G hE hG).comp (measurable_const.prodMk measurable_id)
  have hi := (samplingSecondWeight_integrable h α s hh hα).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTestedSecondWeight_bounds h α E G s t hh hα).1]
      exact (samplingTestedSecondWeight_bounds h α E G s t hh hα).2))
  exact ⟨integral_nonneg (fun t => (samplingTestedSecondWeight_bounds h α E G s t hh hα).1),
    integral_mono_ae hi (samplingSecondWeight_integrable h α s hh hα)
      (Eventually.of_forall (fun t => (samplingTestedSecondWeight_bounds h α E G s t hh hα).2))⟩

theorem samplingTestedSecondDensity_square (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ s ∂unitIntervalMeasure, 0 ≤ samplingTestedSecondDensity h α E G s ∧
      samplingTestedSecondDensity h α E G s ≤ 1/(1-h)) ∧
    (∫ s, samplingTestedSecondDensity h α E G s^2 ∂unitIntervalMeasure) ≤ 1+h^2/(1-h)^2 := by
  let f := samplingTestedSecondDensity h α E G
  let q := samplingIdealSecond h
  let C := 1/(1-h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf := samplingTestedSecondDensity_measurable h α E G hE hG
  have hq := samplingIdealSecond_measurable h hh
  have hnon (s : ℝ) : 0 ≤ f s := (samplingTestedSecondDensity_bounds h α E G hh hα hE hG s).1
  have hle : ∀ᵐ s ∂unitIntervalMeasure, f s ≤ q s :=
    (samplingSecondDensity_le_ideal h α hh hh1 hα).mono (fun s hs =>
      (samplingTestedSecondDensity_bounds h α E G hh hα hE hG s).2.trans hs)
  have hqb (s : ℝ) : 0 ≤ q s ∧ q s ≤ C := (samplingIdealSecond_bounds h s hh hh1).imp_right And.left
  have hq2 (s : ℝ) : q s^2 ≤ C^2 := by nlinarith [(hqb s).1,(hqb s).2]
  have hf2 : ∀ᵐ s ∂unitIntervalMeasure, f s^2 ≤ q s^2 := hle.mono (fun s hs => by nlinarith [hnon s,(hqb s).1])
  have hfi : Integrable (fun s => f s^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (hf.pow_const 2).aestronglyMeasurable (hf2.mono (fun s hs => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hs.trans (hq2 s)))
  have hqi : Integrable (fun s => q s^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (hq.pow_const 2).aestronglyMeasurable (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hq2 s))
  exact ⟨hle.mono (fun s hs => ⟨hnon s,hs.trans (hqb s).2⟩),
    (integral_mono_ae hfi hqi hf2).trans (samplingIdealSecond_square h hh hh1).2⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Moments
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceSamplingWidth_le_half (s : ℕ) : sourceSamplingWidth s ≤ 1/2 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hm0 : 0 ≤ (sourceBlockSize s : ℝ) := by positivity
  have he : sourceSamplingWidth s ≤ (sourceBlockSize s : ℝ)^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hs : 2 ≤ Real.sqrt (sourceBlockSize s : ℝ) := by
    nlinarith [Real.sq_sqrt hm0,Real.sqrt_nonneg (sourceBlockSize s : ℝ)]
  apply he.trans
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hm0,← Real.sqrt_eq_rpow]
  simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)

/-- Exact stage parameters discharge all cutoff/width assumptions in the
source's tested second-diagonal one-coordinate moment bound. -/
theorem sourceSampling_tested_second_moment (s : ℕ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ x ∂unitIntervalMeasure,
      0 ≤ samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x ∧
      samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x ≤ 2) ∧
    (∫ x, samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x^2
      ∂unitIntervalMeasure) ≤ 1+4*(sourceBlockSize s : ℝ)^(-6/5 : ℝ) := by
  have hp := sourceSampling_parameters s
  have hhalf := sourceSamplingWidth_le_half s
  have hden : 0 < 1-sourceSamplingWidth s := by linarith [hp.2.1]
  have hb := samplingTestedSecondDensity_square (sourceSamplingWidth s) (sourceSamplingCutoff s)
    E G hp.1 hp.2.1 hp.2.2 hE hG
  have hi : 1/(1-sourceSamplingWidth s) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have herror : (sourceSamplingWidth s)^2/(1-sourceSamplingWidth s)^2 ≤ 4*(sourceSamplingWidth s)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hsq : (1/4 : ℝ) ≤ (1-sourceSamplingWidth s)^2 := by nlinarith
    nlinarith [sq_nonneg (sourceSamplingWidth s),mul_nonneg (sq_nonneg (sourceSamplingWidth s))
      (show 0 ≤ (1-sourceSamplingWidth s)^2-1/4 by linarith)]
  have he : (sourceSamplingWidth s)^2 = (sourceBlockSize s : ℝ)^(-6/5 : ℝ) := by
    unfold sourceSamplingWidth
    rw [← Real.rpow_natCast,← Real.rpow_mul (sourceBlockSize_pos s).le]
    norm_num
  exact ⟨hb.1.mono (fun x hx => ⟨hx.1,hx.2.trans hi⟩),hb.2.trans (by rw [← he]; linarith)⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedFirstMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem samplingTestedFirstWeight_measurable (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingTestedFirstWeight b h α E G p.1 p.2) := by
  unfold samplingTestedFirstWeight
  exact Measurable.ite ((hE.preimage measurable_fst).inter
    (hG.preimage (sourceFract_measurable.comp (measurable_fst.add measurable_snd))))
    (samplingWeight_measurable b h α) measurable_const

theorem samplingTestedFirstWeight_bounds (b : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ)
    (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingTestedFirstWeight b h α E G s t ∧
    samplingTestedFirstWeight b h α E G s t ≤ samplingWeight b h α s t := by
  have hn := (samplingWeight_bounds b h α s t hh hα).1
  unfold samplingTestedFirstWeight
  split_ifs <;> simp [hn]

theorem samplingWeight_integrable (b : Bool) (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (samplingWeight b h α s) unitIntervalMeasure := by
  apply (integrable_const (max 1 (1/(h*α)))).mono'
    ((samplingWeight_measurable b h α).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    change ‖samplingWeight b h α s t‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (samplingWeight_bounds b h α s t hh hα).1]
    exact (samplingWeight_bounds b h α s t hh hα).2)

theorem samplingTestedFirstDensity_measurable (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingTestedFirstDensity b h α E G) :=
  (samplingTestedFirstWeight_measurable b h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

/-- Tests decrease the exact first marginal, which is at most one. -/
theorem samplingTestedFirstDensity_bounds (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G)
    (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ samplingTestedFirstDensity b h α E G s ∧
    samplingTestedFirstDensity b h α E G s ≤ 1 := by
  have hm : Measurable (samplingTestedFirstWeight b h α E G s) := (samplingTestedFirstWeight_measurable b h α E G hE hG).comp
    (measurable_const.prodMk measurable_id)
  have hi := (samplingWeight_integrable b h α s hh hα).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTestedFirstWeight_bounds b h α E G s t hh hα).1]
      exact (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2))
  refine ⟨integral_nonneg (fun t => (samplingTestedFirstWeight_bounds b h α E G s t hh hα).1), ?_⟩
  calc
    _ ≤ ∫ t, samplingWeight b h α s t ∂unitIntervalMeasure :=
      integral_mono_ae hi (samplingWeight_integrable b h α s hh hα)
        (Eventually.of_forall (fun t => (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2))
    _ ≤ 1 := by
      rw [samplingWeight_first_integral b h α s hh hh1 hα hs]
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · split_ifs <;> norm_num
      · linarith [hs.1]

/-- The first tested marginal has quadratic moment at most one in both
triangular and diagonal coordinates, uniformly in the measurable tests. -/
theorem samplingTestedFirstDensity_square (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingTestedFirstDensity b h α E G s ^ 2 ∂unitIntervalMeasure) ≤ 1 := by
  have hb : ∀ᵐ s ∂unitIntervalMeasure, 0 ≤ samplingTestedFirstDensity b h α E G s ∧
      samplingTestedFirstDensity b h α E G s ≤ 1 :=
    (ae_restrict_mem measurableSet_Ico).mono (fun s hs =>
      samplingTestedFirstDensity_bounds b h α E G hh hh1 hα hE hG s hs)
  have hb2 := hb.mono (fun s hs => show samplingTestedFirstDensity b h α E G s ^ 2 ≤ 1 by nlinarith)
  have hi : Integrable (fun s => samplingTestedFirstDensity b h α E G s ^ 2) unitIntervalMeasure :=
    (integrable_const (1 : ℝ)).mono'
      ((samplingTestedFirstDensity_measurable b h α E G hE hG).pow_const 2).aestronglyMeasurable
      (hb2.mono (fun s hs => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (samplingTestedFirstDensity b h α E G s))]
        exact hs))
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) hb2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SelfMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Squaring the constant-height slice leaves its reciprocal interval length. -/
theorem samplingWeight_square_slice (h α s : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    (∫ t, samplingWeight false h α s t ^ 2 ∂unitIntervalMeasure) =
      if α ≤ samplingDistance s then 1/(h*samplingDistance s) else 0 := by
  have he : (fun t => samplingWeight false h α s t ^ 2) =
      fun t => (1/(h*samplingDistance s))*samplingWeight false h α s t := by
    funext t
    unfold samplingWeight
    simp only [Bool.false_eq_true,ite_false]
    split_ifs <;> ring
  rw [he,integral_const_mul,samplingWeight_first_integral false h α s hh hh1 hα hs]
  simp only [Bool.false_eq_true,ite_false]
  split_ifs <;> simp

/-- Exact logarithmic integral of the cutoff reciprocal distance. -/
theorem samplingDistance_cutoff_integral (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, (if α ≤ samplingDistance s then (samplingDistance s)⁻¹ else 0)
      ∂unitIntervalMeasure) = 2*Real.log (1/(2*α)) := by
  have hab : α ≤ 1-α := by linarith
  have hset : {s | α ≤ samplingDistance s} = Set.Icc α (1-α) := by
    ext s
    simp only [Set.mem_ofPred_eq,samplingDistance,le_min_iff,Set.mem_Icc]
    constructor <;> intro hs <;> constructor <;> linarith [hs.1,hs.2]
  have he : (fun s => if α ≤ samplingDistance s then (samplingDistance s)⁻¹ else 0) =
      (Set.Icc α (1-α)).indicator (fun s => (samplingDistance s)⁻¹) := by
    rw [← hset]
    rfl
  rw [he,integral_indicator measurableSet_Icc]
  unfold unitIntervalMeasure
  rw [Measure.restrict_restrict measurableSet_Icc,Set.inter_eq_left.mpr (show
    Set.Icc α (1-α) ⊆ Set.Ico (0 : ℝ) 1 from fun s hs => ⟨hα.le.trans hs.1,by linarith [hs.2]⟩),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
  have hc : ContinuousOn (fun s => (samplingDistance s)⁻¹) (Set.Icc α (1-α)) := by
    apply ContinuousOn.inv₀ (by unfold samplingDistance; fun_prop)
    intro s hs
    have hd : 0 < samplingDistance s := lt_min (hα.trans_le hs.1) (by linarith [hs.2])
    exact hd.ne'
  have hi : IntervalIntegrable (fun s => (samplingDistance s)⁻¹) volume α (1-α) := hc.intervalIntegrable_of_Icc hab
  have hleft : IntervalIntegrable (fun s => (samplingDistance s)⁻¹) volume α (1/2) :=
    hi.mono_set (by rw [Set.uIcc_of_le hα1,Set.uIcc_of_le hab]; intro s hs; exact ⟨hs.1,by linarith [hs.2]⟩)
  have hright : IntervalIntegrable (fun s => (samplingDistance s)⁻¹) volume (1/2) (1-α) :=
    hi.mono_set (by rw [Set.uIcc_of_le (show (1/2 : ℝ) ≤ 1-α by linarith),Set.uIcc_of_le hab]; intro s hs; exact ⟨by linarith [hs.1],hs.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
  have hl : (∫ s in α..(1/2 : ℝ), (samplingDistance s)⁻¹) = Real.log ((1/2)/α) := by
    calc
      _ = ∫ s in α..(1/2 : ℝ), s⁻¹ := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hα1]
        intro s hs
        change (min s (1-s))⁻¹ = s⁻¹
        rw [min_eq_left (by linarith [hs.2])]
      _ = _ := integral_inv_of_pos hα (by norm_num)
  have hr : (∫ s in (1/2 : ℝ)..(1-α), (samplingDistance s)⁻¹) = Real.log ((1/2)/α) := by
    calc
      _ = ∫ s in (1/2 : ℝ)..(1-α), (1-s)⁻¹ := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (show (1/2 : ℝ) ≤ 1-α by linarith)]
        intro s hs
        change (min s (1-s))⁻¹ = (1-s)⁻¹
        rw [min_eq_right (by linarith [hs.1])]
      _ = ∫ s in α..(1/2 : ℝ), s⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => s⁻¹) 1]
        norm_num
      _ = _ := integral_inv_of_pos hα (by norm_num)
  rw [hl,hr,show (1/2 : ℝ)/α = 1/(2*α) by ring]
  ring

theorem samplingWeight_square_integral (h α : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, ∫ t, samplingWeight false h α s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) = (2/h)*Real.log (1/(2*α)) := by
  calc
    _ = ∫ s, (1/h)*(if α ≤ samplingDistance s then (samplingDistance s)⁻¹ else 0)
        ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [show ∀ᵐ s ∂unitIntervalMeasure, s ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with s hs
      rw [samplingWeight_square_slice h α s hh hh1 hα hs]
      split_ifs <;> simp [div_eq_mul_inv,mul_comm]
    _ = _ := by
      rw [integral_const_mul,samplingDistance_cutoff_integral α hα hα1]
      ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedSelfMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- A bounded measurable real function has an integrable square on a finite measure. -/
theorem sampling_square_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → ℝ) (C : ℝ) (hm : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ C) : Integrable (fun x => f x ^ 2) μ := by
  apply (integrable_const (C^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))]
    nlinarith [(hb x).1,(hb x).2])

/-- Squared weights are integrable jointly, permitting the source's Fubini step. -/
theorem samplingWeight_square_integrable (b : Bool) (h α : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (fun p : ℝ × ℝ => samplingWeight b h α p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
  sampling_square_integrable _ _ (max 1 (1/(h*α))) (samplingWeight_measurable b h α)
    (fun p => samplingWeight_bounds b h α p.1 p.2 hh hα)

/-- Haar translation preserves the untested self-pair moment in the second
orientation, with the source's order of both integrations. -/
theorem samplingSecondWeight_square_integral (h α : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, ∫ t, samplingSecondWeight h α s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) = (2/h)*Real.log (1/(2*α)) := by
  have hi : Integrable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) (samplingSecondWeight_measurable h α)
      (fun p => samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα)
  rw [integral_integral_swap hi]
  calc
    _ = ∫ t, ∫ s, samplingWeight false h α s t ^ 2 ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hm : AEStronglyMeasurable (fun s => samplingWeight false h α s t ^ 2) unitIntervalMeasure :=
        (((samplingWeight_measurable false h α).comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
      have hp := unitInterval_rotate_preserving (-t)
      have he := integral_map hp.measurable.aemeasurable (show AEStronglyMeasurable
        (fun s => samplingWeight false h α s t ^ 2) (unitIntervalMeasure.map (fun s => Int.fract (s+ -t))) from
          hp.map_eq.symm ▸ hm)
      rw [hp.map_eq] at he
      simpa [samplingSecondWeight,sub_eq_add_neg] using he.symm
    _ = _ := by
      rw [← integral_integral_swap (samplingWeight_square_integrable false h α hh hα),
        samplingWeight_square_integral h α hh hh1 hα hα1]

/-- Tests decrease the diagonal self-pair moment in the first orientation. -/
theorem samplingTestedFirstWeight_square_integral (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hα1 : α ≤ 1/2)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ t, samplingTestedFirstWeight false h α E G s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤ (2/h)*Real.log (1/(2*α)) := by
  have hb (s t : ℝ) := samplingTestedFirstWeight_bounds false h α E G s t hh hα
  have hm := samplingTestedFirstWeight_measurable false h α E G hE hG
  have hbig := samplingWeight_square_integrable false h α hh hα
  have hsmall : Integrable (fun p : ℝ × ℝ => samplingTestedFirstWeight false h α E G p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) hm
      (fun p => ⟨(hb p.1 p.2).1,(hb p.1 p.2).2.trans (samplingWeight_bounds false h α p.1 p.2 hh hα).2⟩)
  rw [← samplingWeight_square_integral h α hh hh1 hα hα1,
    ← integral_prod _ hsmall,← integral_prod _ hbig]
  apply integral_mono_ae hsmall hbig
  exact Eventually.of_forall (fun p => by
    nlinarith [(hb p.1 p.2).1,(hb p.1 p.2).2,
      (samplingWeight_bounds false h α p.1 p.2 hh hα).1])

/-- Tests decrease the diagonal self-pair moment in the second orientation. -/
theorem samplingTestedSecondWeight_square_integral (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hα1 : α ≤ 1/2)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ t, samplingTestedSecondWeight h α E G s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤ (2/h)*Real.log (1/(2*α)) := by
  have hb (s t : ℝ) := samplingTestedSecondWeight_bounds h α E G s t hh hα
  have hm := samplingTestedSecondWeight_measurable h α E G hE hG
  have hbig : Integrable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) (samplingSecondWeight_measurable h α)
      (fun p => samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα)
  have hsmall : Integrable (fun p : ℝ × ℝ => samplingTestedSecondWeight h α E G p.1 p.2 ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    sampling_square_integrable _ _ (max 1 (1/(h*α))) hm
      (fun p => ⟨(hb p.1 p.2).1,(hb p.1 p.2).2.trans
        (samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα).2⟩)
  rw [← samplingSecondWeight_square_integral h α hh hh1 hα hα1,
    ← integral_prod _ hsmall,← integral_prod _ hbig]
  apply integral_mono_ae hsmall hbig
  exact Eventually.of_forall (fun p => by
    nlinarith [(hb p.1 p.2).1,(hb p.1 p.2).2,
      (samplingWeight_bounds false h α (Int.fract (p.1-p.2)) p.2 hh hα).1])

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_OrientedMoments
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem samplingOrientedWeight_measurable (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingOrientedWeight r b h α E G p.1 p.2) := by
  cases r
  · exact samplingTestedFirstWeight_measurable b h α E G hE hG
  · unfold samplingOrientedWeight
    simp only [ite_true]
    exact Measurable.ite ((hE.preimage (sourceFract_measurable.comp
      (measurable_fst.sub measurable_snd))).inter (hG.preimage measurable_fst))
      ((samplingWeight_measurable b h α).comp
        ((sourceFract_measurable.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)) measurable_const

theorem samplingOrientedWeight_bounds (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hα : 0 < α) (s t : ℝ) :
    0 ≤ samplingOrientedWeight r b h α E G s t ∧
    samplingOrientedWeight r b h α E G s t ≤ max 1 (1/(h*α)) := by
  cases r
  · exact ⟨(samplingTestedFirstWeight_bounds b h α E G s t hh hα).1,
      (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2.trans
        (samplingWeight_bounds b h α s t hh hα).2⟩
  · unfold samplingOrientedWeight
    simp only [ite_true]
    split_ifs
    · exact samplingWeight_bounds b h α _ _ hh hα
    · exact ⟨le_rfl,(by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)⟩

theorem samplingOrientedWeight_triangular_bounds (r : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) :
    0 ≤ samplingOrientedWeight r true h α E G s t ∧
    samplingOrientedWeight r true h α E G s t ≤ 1 := by
  cases r <;> unfold samplingOrientedWeight samplingTestedFirstWeight samplingWeight <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> norm_num

theorem samplingOrientedDensity_measurable (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingOrientedDensity r b h α E G) :=
  (samplingOrientedWeight_measurable r b h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

/-- Both triangular orientations have tested marginal densities between zero and one. -/
theorem samplingOrientedDensity_triangular_bounds (r : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) (s : ℝ) :
    0 ≤ samplingOrientedDensity r true h α E G s ∧
    samplingOrientedDensity r true h α E G s ≤ 1 := by
  have hm : Measurable (samplingOrientedWeight r true h α E G s) :=
    (samplingOrientedWeight_measurable r true h α E G hE hG).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (samplingOrientedWeight r true h α E G s) unitIntervalMeasure :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingOrientedWeight_triangular_bounds r h α E G s t).1]
      exact (samplingOrientedWeight_triangular_bounds r h α E G s t).2))
  refine ⟨integral_nonneg (fun t => (samplingOrientedWeight_triangular_bounds r h α E G s t).1),?_⟩
  simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun t => (samplingOrientedWeight_triangular_bounds r h α E G s t).2))

theorem samplingOrientedDensity_triangular_square (r : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingOrientedDensity r true h α E G s ^ 2 ∂unitIntervalMeasure) ≤ 1 := by
  have hb := samplingOrientedDensity_triangular_bounds r h α E G hE hG
  have hi := sampling_square_integrable unitIntervalMeasure _ 1
    (samplingOrientedDensity_measurable r true h α E G hE hG) hb
  simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun s => show samplingOrientedDensity r true h α E G s ^ 2 ≤ 1 by
      nlinarith [(hb s).1,(hb s).2]))

theorem sourceSampling_oriented_moment (stage : ℕ) (r b : Bool) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ s ∂unitIntervalMeasure,
      0 ≤ samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ∧
      samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ≤ 2) ∧
    (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ^ 2
      ∂unitIntervalMeasure) ≤ 1+4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) := by
  have hp := sourceSampling_parameters stage
  have herr : (0 : ℝ) ≤ 4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) := by positivity
  cases r
  · have hb : ∀ᵐ s ∂unitIntervalMeasure,
        0 ≤ samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ∧
        samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ≤ 1 :=
      (ae_restrict_mem measurableSet_Ico).mono (fun s hs => samplingTestedFirstDensity_bounds b _ _ E G
        hp.1 hp.2.1 hp.2.2 hE hG s hs)
    refine ⟨hb.mono (fun s hs => ⟨hs.1,hs.2.trans (by norm_num)⟩),?_⟩
    exact (samplingTestedFirstDensity_square b _ _ E G hp.1 hp.2.1 hp.2.2 hE hG).trans (by linarith)
  · cases b
    · exact sourceSampling_tested_second_moment stage E G hE hG
    · refine ⟨Eventually.of_forall (fun s => ?_),?_⟩
      · have hb := samplingOrientedDensity_triangular_bounds true (sourceSamplingWidth stage)
          (sourceSamplingCutoff stage) E G hE hG s
        exact ⟨hb.1,hb.2.trans (by norm_num)⟩
      · exact (samplingOrientedDensity_triangular_square true _ _ E G hE hG).trans (by linarith)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_IdealProduct
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- The actual source prefix dimension, including the current block. -/
theorem sourceSamplingPrefix_card (stage : ℕ) :
    (sourceSamplingPrefix stage).card = (sourceStageState stage).d+sourceBlockSize stage := by
  unfold sourceSamplingPrefix CouplingParameters.blockPrefix
  simp only [Finset.card_sigma,Finset.card_univ,Fintype.card_fin]
  change (∑ i ∈ range (stage+1), (sourceStage i).m) = _
  rw [sum_range_succ,← sourceStage_previous_size]
  rfl

theorem sourceSamplingPrefix_card_bound (stage : ℕ) :
    ((sourceSamplingPrefix stage).card : ℝ) ≤ (101/100 : ℝ)*sourceBlockSize stage := by
  rw [sourceSamplingPrefix_card,Nat.cast_add]
  have hp := (sourceStage stage).previous_size
  change ((sourceStageState stage).d : ℝ) ≤ (sourceBlockSize stage : ℝ)/100 at hp
  linarith

/-- The small quadratic coordinate errors stay bounded in the growing prefix. -/
theorem sourceSampling_prefix_quadratic_budget (stage : ℕ) :
    ((sourceSamplingPrefix stage).card : ℝ)*(4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ)) ≤ 5 := by
  have hm := sourceBlockSize_pos stage
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith
  have he : (sourceBlockSize stage : ℝ)*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) =
      (sourceBlockSize stage : ℝ)^(-1/5 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (sourceBlockSize stage : ℝ)]
    rw [← Real.rpow_add hm]
    norm_num
  have hp : (sourceBlockSize stage : ℝ)^(-1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  calc
    _ ≤ ((101/100 : ℝ)*sourceBlockSize stage)*(4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ)) :=
      mul_le_mul_of_nonneg_right (sourceSamplingPrefix_card_bound stage) (by positivity)
    _ = (101/25 : ℝ)*(sourceBlockSize stage : ℝ)^(-1/5 : ℝ) := by rw [← he]; ring
    _ ≤ 5 := by linarith

theorem sourceSamplingIdealDensity_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Measurable (sourceSamplingIdealDensity stage r b E G) :=
  Finset.measurable_prod _ (fun i _ =>
    (samplingOrientedDensity_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).comp (measurable_pi_apply i))

/-- Exact product factorization of the ideal marginal's quadratic moment. -/
theorem sourceSamplingIdealDensity_square (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage r b E G x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
      ∏ i ∈ sourceSamplingPrefix stage,
        ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ^ 2
          ∂unitIntervalMeasure := by
  simp only [sourceSamplingIdealDensity,← Finset.prod_pow]
  exact integral_infinitePi_finset_prod _ _ _ (fun i =>
    (samplingOrientedDensity_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).pow_const 2)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_SelfMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceSamplingCutoff_le_half (s : ℕ) : sourceSamplingCutoff s ≤ 1/2 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hp := sourceBlockSize_pos s
  calc
    sourceSamplingCutoff s ≤ (sourceBlockSize s : ℝ)^(-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = 1/(sourceBlockSize s : ℝ) := by rw [Real.rpow_neg_one,one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem sourceSampling_log_self_bound (s : ℕ) :
    (2/sourceSamplingWidth s)*Real.log (1/(2*sourceSamplingCutoff s)) ≤
      4*(sourceBlockSize s : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize s : ℝ) := by
  have hp := sourceSampling_parameters s
  have hm := sourceBlockSize_pos s
  have hl : Real.log (1/(2*sourceSamplingCutoff s)) ≤ Real.log (1/sourceSamplingCutoff s) :=
    Real.log_le_log (one_div_pos.mpr (mul_pos (by norm_num) hp.2.2)) (one_div_le_one_div_of_le hp.2.2 (by linarith [hp.2.2]))
  have he : Real.log (1/sourceSamplingCutoff s) = 2*Real.log (sourceBlockSize s : ℝ) := by
    unfold sourceSamplingCutoff
    rw [one_div,Real.log_inv,Real.log_rpow hm]
    ring
  have hw : (sourceSamplingWidth s)⁻¹ = (sourceBlockSize s : ℝ)^(3/5 : ℝ) := by
    unfold sourceSamplingWidth
    rw [show (-3/5 : ℝ) = -(3/5) by ring,Real.rpow_neg hm.le,inv_inv]
  calc
    _ ≤ (2/sourceSamplingWidth s)*(2*Real.log (sourceBlockSize s : ℝ)) :=
      mul_le_mul_of_nonneg_left (hl.trans_eq he) (div_nonneg (by norm_num) hp.1.le)
    _ = _ := by rw [div_eq_mul_inv,hw]; ring

/-- All tested source weights have the logarithmic self-pair bound in both
orientations. The harmless extra 1 includes triangular coordinates. -/
theorem sourceSampling_oriented_self_moment (stage : ℕ) (r b : Bool) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ t, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s t ^ 2
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
      1+4*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ) := by
  have hp := sourceSampling_parameters stage
  have hc := sourceSamplingCutoff_le_half stage
  have hlog : 0 ≤ Real.log (sourceBlockSize stage : ℝ) := Real.log_nonneg (by
    have hm : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith)
  have herr : (0 : ℝ) ≤ 4*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ) := by positivity
  cases b
  · have hb : (∫ s, ∫ t, samplingOrientedWeight r false (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s t ^ 2
        ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
        (2/sourceSamplingWidth stage)*Real.log (1/(2*sourceSamplingCutoff stage)) := by
      cases r
      · exact samplingTestedFirstWeight_square_integral _ _ E G hp.1 hp.2.1 hp.2.2 hc hE hG
      · exact samplingTestedSecondWeight_square_integral _ _ E G hp.1 hp.2.1 hp.2.2 hc hE hG
    exact (hb.trans (sourceSampling_log_self_bound stage)).trans (by linarith)
  · have hm := samplingOrientedWeight_measurable r true (sourceSamplingWidth stage)
      (sourceSamplingCutoff stage) E G hE hG
    have hb := samplingOrientedWeight_triangular_bounds r (sourceSamplingWidth stage)
      (sourceSamplingCutoff stage) E G
    have hi := sampling_square_integrable (unitIntervalMeasure.prod unitIntervalMeasure) _ 1 hm
      (fun p => hb p.1 p.2)
    rw [← integral_prod _ hi]
    have hle : (∫ p : ℝ × ℝ, samplingOrientedWeight r true (sourceSamplingWidth stage)
        (sourceSamplingCutoff stage) E G p.1 p.2 ^ 2 ∂unitIntervalMeasure.prod unitIntervalMeasure) ≤ 1 := by
      simpa using integral_mono_ae hi (integrable_const (1 : ℝ))
        (Eventually.of_forall (fun p => by nlinarith [(hb p.1 p.2).1,(hb p.1 p.2).2]))
    exact hle.trans (by linarith)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_PhaseSelfMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Marginal phase domination controls the joint self-pair integral.
This is the source's one-phase step before taking coordinate products. -/
theorem sampling_phase_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hdom : μ.map X ≤ (2 : ℝ≥0∞) • unitIntervalMeasure)
    (u : ℝ → ℝ → ℝ) (C : ℝ) (hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2))
    (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C) :
    (∫ s, ∫ ω, u s (X ω)^2 ∂μ ∂unitIntervalMeasure) ≤
      2*(∫ s, ∫ t, u s t^2 ∂unitIntervalMeasure ∂unitIntervalMeasure) := by
  have hΩ : Measurable (fun p : ℝ × Ω => u p.1 (X p.2)) :=
    hu.comp (measurable_fst.prodMk (hX.comp measurable_snd))
  have hiΩ := sampling_square_integrable (unitIntervalMeasure.prod μ) _ C hΩ
    (fun p => hb p.1 (X p.2))
  have hiU := sampling_square_integrable (unitIntervalMeasure.prod unitIntervalMeasure) _ C hu
    (fun p => hb p.1 p.2)
  have hpoint (s : ℝ) : (∫ ω, u s (X ω)^2 ∂μ) ≤ 2*(∫ t, u s t^2 ∂unitIntervalMeasure) := by
    have hm : Measurable (fun t => u s t) := hu.comp (measurable_const.prodMk measurable_id)
    have hi := sampling_square_integrable unitIntervalMeasure _ C hm (hb s)
    have hbig := hi.smul_measure (c := (2 : ℝ≥0∞)) (by norm_num)
    have hle := integral_mono_measure hdom (Eventually.of_forall (fun t => sq_nonneg (u s t))) hbig
    rw [integral_map hX.aemeasurable (hm.pow_const 2).aestronglyMeasurable,
      integral_smul_measure] at hle
    simpa using hle
  calc
    _ ≤ ∫ s, 2*(∫ t, u s t^2 ∂unitIntervalMeasure) ∂unitIntervalMeasure :=
      integral_mono_ae hiΩ.integral_prod_left (hiU.integral_prod_left.const_mul 2)
        (Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

/-- Actual angle expectation of the tested self-pair, at every admissible
selected power, for all source orientations and coordinate types. -/
theorem sourceSampling_phase_self_moment (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage)
    (r b : Bool) (E G : Set ℝ) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      E G s (Int.fract ((n : ℝ)*θ i)) ^ 2 ∂sourceAngleLaw ∂unitIntervalMeasure) ≤
      2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ) := by
  have hp := sourceSampling_parameters stage
  have hbound := sampling_phase_square_bound sourceAngleLaw (fun θ => Int.fract ((n : ℝ)*θ i))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    (sourceSampling_phase_domination stage hs i hi n hn)
    (samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G)
    (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))
    (samplingOrientedWeight_measurable r b _ _ E G hE hG)
    (samplingOrientedWeight_bounds r b _ _ E G hp.1 hp.2.2)
  have hself := sourceSampling_oriented_self_moment stage r b E G hE hG
  exact hbound.trans (by nlinarith)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_ProductMoments
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceSamplingProduct_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingProduct stage r b E G n p.1 p.2) := by
  unfold sourceSamplingProduct
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      (p.2 i,Int.fract ((n : ℝ)*p.1 i))) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk
      (sourceFract_measurable.comp (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)))
  exact (samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i) (hE i) (hG i)).comp hm

theorem sourceSamplingProduct_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (n : ℤ) (θ x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingProduct stage r b E G n θ x ∧
    sourceSamplingProduct stage r b E G n θ x ≤
      (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) := samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2
    (x i) (Int.fract ((n : ℝ)*θ i))
  refine ⟨prod_nonneg (fun i _ => (hb i).1),?_⟩
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) :=
      prod_le_prod (fun i _ => (hb i).1) (fun i _ => (hb i).2)
    _ = _ := by simp

/-- Exact coordinate factorization under the two actual infinite product laws.
Dependence of the two phases within one coordinate is retained in each factor. -/
theorem sourceSamplingProduct_inner_factorization (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n k : ℤ) :
    (∫ x, ∫ θ, sourceSamplingProduct stage r b E G n θ x * sourceSamplingProduct stage r b E G k θ x
      ∂sourceAngleLaw ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
    ∏ i ∈ sourceSamplingPrefix stage,
      ∫ s, ∫ θ, samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s (Int.fract ((n : ℝ)*θ i)) *
        samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s (Int.fract ((k : ℝ)*θ i)) ∂sourceAngleLaw ∂unitIntervalMeasure := by
  let u (i : SourceCoordinate) := samplingOrientedWeight r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i)
  let F (i : SourceCoordinate) (s a : ℝ) := u i s (Int.fract ((n : ℝ)*a))*u i s (Int.fract ((k : ℝ)*a))
  have hF (i : SourceCoordinate) : Measurable (fun p : ℝ × ℝ => F i p.1 p.2) := by
    have hu := samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (hE i) (hG i)
    exact (hu.comp (measurable_fst.prodMk (sourceFract_measurable.comp (measurable_const.mul measurable_snd)))).mul
      (hu.comp (measurable_fst.prodMk (sourceFract_measurable.comp (measurable_const.mul measurable_snd))))
  calc
    _ = ∫ x, ∏ i ∈ sourceSamplingPrefix stage, ∫ a, F i (x i) a ∂sourceAngleMarginal i
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [sourceSamplingProduct,← Finset.prod_mul_distrib]
      exact integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).comp (measurable_const.prodMk measurable_id))
    _ = ∏ i ∈ sourceSamplingPrefix stage, ∫ s, ∫ a, F i s a ∂sourceAngleMarginal i ∂unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).stronglyMeasurable.integral_prod_right.measurable)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with s
      have hm : Measurable (fun a => F i s a) := (hF i).comp (measurable_const.prodMk measurable_id)
      rw [← sourceAngleLaw_coordinate i,integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable]

/-- The actual full-prefix self-pair estimate, with the source's angle
expectation outside the L2 square integral. -/
theorem sourceSamplingProduct_self_moment (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    (∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw) ≤
      (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ))^(sourceSamplingPrefix stage).card := by
  have hint := sampling_square_integrable
    (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)))
    (fun p => sourceSamplingProduct stage r b E G n p.1 p.2)
    ((max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card)
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)
  rw [integral_integral_swap hint]
  simp only [pow_two]
  rw [sourceSamplingProduct_inner_factorization stage r b E G hE hG n n]
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage,
        (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun s => integral_nonneg (fun θ => mul_self_nonneg _))
      · intro i hi
        have hip : i.1 ≤ stage := by
          have ht := (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mp hi
          omega
        simpa only [pow_two] using sourceSampling_phase_self_moment stage hs i hip n hn r (b i)
          (E i) (G i) (hE i) (hG i)
    _ = _ := by simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_LayerCake
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- A bounded measurable real function on a finite measure space is integrable. -/
theorem sampling_integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hb x)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_IntegratedCorrelation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Bounded nonnegative products are integrable, uniformly in their parameters. -/
theorem sampling_bounded_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (C : ℝ) (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    Integrable (fun x => f x*g x) μ := by
  apply sampling_integrable_bounded μ (fun x => f x*g x) (hf.mul hg) (C^2)
  intro x
  rw [abs_of_nonneg (mul_nonneg (hfb x).1 (hgb x).1)]
  calc
    f x*g x ≤ C*C := mul_le_mul (hfb x).2 (hgb x).2 (hgb x).1 ((hfb x).1.trans (hfb x).2)
    _ = C^2 := by ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_MixedCorrelation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- A bounded nonnegative coordinate kernel has a measurable bounded mean. -/
theorem sampling_kernel_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : ℝ → Ω → ℝ)
    (hu : Measurable (fun p : ℝ × Ω => u p.1 p.2)) (C : ℝ)
    (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C) :
    Measurable (fun s => ∫ t, u s t ∂μ) ∧
    ∀ s, 0 ≤ (∫ t, u s t ∂μ) ∧ (∫ t, u s t ∂μ) ≤ C := by
  refine ⟨hu.stronglyMeasurable.integral_prod_right.measurable,?_⟩
  intro s
  have hi : Integrable (u s) μ := sampling_integrable_bounded μ _
    (hu.comp (measurable_const.prodMk measurable_id)) C
    (fun t => by rw [abs_of_nonneg (hb s t).1]; exact (hb s t).2)
  exact ⟨integral_nonneg (fun t => (hb s t).1),by
    simpa using integral_mono_ae hi (integrable_const C) (Eventually.of_forall (fun t => (hb s t).2))⟩

/-- The mixed coordinate factor inherits a relative one-phase error.
The ideal moment may vanish; no division by it occurs. -/
theorem sampling_integrated_mixed_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (u : ℝ → ℝ → ℝ) (hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2))
    (C ε : ℝ) (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C)
    (he : ∀ s, |(∫ x, u s (X x) ∂μ)-(∫ t, u s t ∂unitIntervalMeasure)| ≤
      ε*(∫ t, u s t ∂unitIntervalMeasure)) :
    |(∫ s, (∫ t, u s t ∂unitIntervalMeasure)*(∫ x, u s (X x) ∂μ) ∂unitIntervalMeasure)-
      (∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure)| ≤
      ε*(∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure) := by
  let a := fun s => ∫ t, u s t ∂unitIntervalMeasure
  let b := fun s => ∫ x, u s (X x) ∂μ
  have ha := sampling_kernel_mean unitIntervalMeasure u hu C hb
  have hbu : Measurable (fun p : ℝ × Ω => u p.1 (X p.2)) :=
    hu.comp (measurable_fst.prodMk (hX.comp measurable_snd))
  have hbb := sampling_kernel_mean μ (fun s x => u s (X x)) hbu C (fun s x => hb s (X x))
  have hai : Integrable (fun s => a s^2) unitIntervalMeasure := by
    simpa only [pow_two] using sampling_bounded_product_integrable unitIntervalMeasure a a ha.1 ha.1 C ha.2 ha.2
  have habi := sampling_bounded_product_integrable unitIntervalMeasure a b ha.1 hbb.1 C ha.2 hbb.2
  change |(∫ s, a s*b s ∂unitIntervalMeasure)-(∫ s, a s^2 ∂unitIntervalMeasure)| ≤
    ε*(∫ s, a s^2 ∂unitIntervalMeasure)
  rw [← integral_sub habi hai,← integral_const_mul]
  apply (show |(∫ s, a s*b s-a s^2 ∂unitIntervalMeasure)| ≤
      ∫ s, ε*a s^2 ∂unitIntervalMeasure from ?_)
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hai.const_mul ε)
  apply Eventually.of_forall
  intro s
  rw [Real.norm_eq_abs]
  calc
    |a s*b s-a s^2| = a s*|b s-a s| := by
      rw [show a s*b s-a s^2 = a s*(b s-a s) by ring,abs_mul,abs_of_nonneg (ha.2 s).1]
    _ ≤ a s*(ε*a s) := mul_le_mul_of_nonneg_left (he s) (ha.2 s).1
    _ = ε*a s^2 := by ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_SingleCorrelation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- The source powers make the single-phase relative error at most m^-80. -/
theorem sourceSampling_single_phase_budget (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    1/((n : ℝ)*sourceAngleUnit i) ≤ (sourceBlockSize stage : ℝ)^(-80 : ℝ) := by
  let m : ℝ := sourceBlockSize stage
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm2 : 2 ≤ m := by dsimp [m]; exact_mod_cast (show 2 ≤ sourceBlockSize stage by omega)
  have hspec := (sourceSamplingPowers_spec stage hs).1 n hn
  have hQ : m^(83 : ℝ) ≤ samplingQ (sourceBlockSize stage) := by
    unfold samplingQ
    change m^(83 : ℝ) ≤ m^((7/10 : ℝ)*m)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hh : (200000 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast hs
      linarith)
  have hN : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤ m^2 := by
    have hh : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤
        (sourceBlockSize stage : ℝ)*(sourceStageState stage).K := by exact_mod_cast sourceFrequencyScale_monotone hi
    have hK : ((sourceStageState stage).K : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_K
    dsimp [m]
    nlinarith
  have hp : 0 < (n : ℝ) := by exact_mod_cast hspec.2.2
  have h82 : m^(82 : ℝ) ≤ (n : ℝ) := by
    have he : m^(83 : ℝ) = m^(82 : ℝ)*m := by
      rw [show (83 : ℝ) = 82+1 by norm_num,Real.rpow_add hm,Real.rpow_one]
    have hh : 2*m^(82 : ℝ) ≤ m^(83 : ℝ) := by rw [he]; nlinarith [Real.rpow_pos_of_pos hm (82 : ℝ)]
    nlinarith [hspec.1]
  have hlen : m^(80 : ℝ) ≤ (n : ℝ)*sourceAngleUnit i := by
    unfold sourceAngleUnit
    rw [mul_one_div,le_div_iff₀ (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))]
    calc
      _ ≤ m^(80 : ℝ)*m^2 := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = m^(82 : ℝ) := by rw [← Real.rpow_natCast,← Real.rpow_add hm]; norm_num
      _ ≤ _ := h82
  have he := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hm (80 : ℝ)) hlen
  simpa only [m,one_div,Real.rpow_neg (sourceBlockSize_pos stage).le] using he

/-- Actual full-angle single-phase test, with all source sampling hypotheses. -/
theorem sourceSampling_single_phase_relative (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage)
    (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ g t) (hgm : Measurable g) (hgi : Integrable g unitIntervalMeasure) :
    |(∫ θ, g (Int.fract ((n : ℝ)*θ i)) ∂sourceAngleLaw)-(∫ t, g t ∂unitIntervalMeasure)| ≤
      (sourceBlockSize stage : ℝ)^(-80 : ℝ)*(∫ t, g t ∂unitIntervalMeasure) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast ((sourceSamplingPowers_spec stage hs).1 n hn).2.2
  have hh := sourceAngle_single_phase_test i (n : ℝ) hnp (sourceSampling_phase_length stage hs i hi n hn) g hg hgm hgi
  have hm : Measurable (fun t : ℝ => g (Int.fract ((n : ℝ)*t))) :=
    hgm.comp (sourceFract_measurable.comp (measurable_const.mul measurable_id))
  rw [← sourceAngleLaw_coordinate i,integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (sourceSampling_single_phase_budget stage hs i hi n hn) (integral_nonneg hg))

/-- The actual mixed q_n/Z_l^0 coordinate factor, for every orientation and
all measurable tests, has error at most 5*m^-80. -/
theorem sourceSampling_coordinate_mixed_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage)
    (r b : Bool) (E G : Set ℝ) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    |(∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s *
        (∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          E G s (Int.fract ((n : ℝ)*θ i)) ∂sourceAngleLaw) ∂unitIntervalMeasure)-
      (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s^2 ∂unitIntervalMeasure)| ≤
      5*(sourceBlockSize stage : ℝ)^(-80 : ℝ) := by
  let u := samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G
  let C := max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage))
  have hp := sourceSampling_parameters stage
  have hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2) := samplingOrientedWeight_measurable r b _ _ E G hE hG
  have hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C := samplingOrientedWeight_bounds r b _ _ E G hp.1 hp.2.2
  have he := sampling_integrated_mixed_error sourceAngleLaw (fun θ => Int.fract ((n : ℝ)*θ i))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    u hu C ((sourceBlockSize stage : ℝ)^(-80 : ℝ)) hb (fun s =>
      sourceSampling_single_phase_relative stage hs i hi n hn (u s) (fun t => (hb s t).1)
        (hu.comp (measurable_const.prodMk measurable_id))
        (sampling_integrable_bounded unitIntervalMeasure (u s)
          (hu.comp (measurable_const.prodMk measurable_id)) C (fun t => by
            rw [abs_of_nonneg (hb s t).1]; exact (hb s t).2)))
  apply he.trans
  have hA := (sourceSampling_oriented_moment stage r b E G hE hG).2
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have h := (sourceStage stage).m_ge_100
    exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
  have hpow : (sourceBlockSize stage : ℝ)^(-6/5 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  have hA5 : (∫ s, (∫ t, u s t ∂unitIntervalMeasure)^2 ∂unitIntervalMeasure) ≤ 5 := by
    exact hA.trans (by linarith)
  nlinarith [Real.rpow_nonneg (sourceBlockSize_pos stage).le (-80 : ℝ)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CrossProducts
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- A global bound used only to justify finite-stage integrations. -/
theorem sourceSamplingIdealDensity_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingIdealDensity stage r b E G x ∧
      sourceSamplingIdealDensity stage r b E G x ≤
        (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) := (sampling_kernel_mean unitIntervalMeasure
    (samplingOrientedWeight r (b i) _ _ (E i) (G i))
    (samplingOrientedWeight_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i))
    (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))
    (samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2)).2
  refine ⟨prod_nonneg (fun i _ => (hb i (x i)).1),?_⟩
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) :=
      prod_le_prod (fun i _ => (hb i (x i)).1) (fun i _ => (hb i (x i)).2)
    _ = _ := by simp

/-- Exact mixed factorization for q_n and the actual ideal density on the
full countable Haar space. -/
theorem sourceSamplingProduct_mixed_factorization (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    (∫ x, ∫ θ, sourceSamplingProduct stage r b E G n θ x * sourceSamplingIdealDensity stage r b E G x
      ∂sourceAngleLaw ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
    ∏ i ∈ sourceSamplingPrefix stage,
      ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s *
        (∫ θ, samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s (Int.fract ((n : ℝ)*θ i)) ∂sourceAngleLaw) ∂unitIntervalMeasure := by
  let u (i : SourceCoordinate) := samplingOrientedWeight r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i)
  let a (i : SourceCoordinate) := samplingOrientedDensity r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i)
  let F (i : SourceCoordinate) (s t : ℝ) := u i s (Int.fract ((n : ℝ)*t))*a i s
  have hF (i : SourceCoordinate) : Measurable (fun p : ℝ × ℝ => F i p.1 p.2) := by
    have hu := samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (hE i) (hG i)
    have ha := samplingOrientedDensity_measurable r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (hE i) (hG i)
    exact (hu.comp (measurable_fst.prodMk (sourceFract_measurable.comp (measurable_const.mul measurable_snd)))).mul
      (ha.comp measurable_fst)
  calc
    _ = ∫ x, ∏ i ∈ sourceSamplingPrefix stage, ∫ t, F i (x i) t ∂sourceAngleMarginal i
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [sourceSamplingProduct,sourceSamplingIdealDensity,← Finset.prod_mul_distrib]
      exact integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).comp (measurable_const.prodMk measurable_id))
    _ = ∏ i ∈ sourceSamplingPrefix stage, ∫ s, ∫ t, F i s t ∂sourceAngleMarginal i ∂unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).stronglyMeasurable.integral_prod_right.measurable)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with s
      have hm : Measurable (fun t => F i s t) := (hF i).comp (measurable_const.prodMk measurable_id)
      rw [← sourceAngleLaw_coordinate i,integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable]
      dsimp [F,u,a]
      rw [integral_mul_const,mul_comm]

/-- Fubini is justified for every finite-stage pair of actual summands. -/
theorem sourceSamplingProduct_pair_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n k : ℤ) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingProduct stage r b E G n p.1 p.2*sourceSamplingProduct stage r b E G k p.1 p.2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) :=
  sampling_bounded_product_integrable _ _ _
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    (sourceSamplingProduct_measurable stage r b E G hE hG k) _
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)
    (fun p => sourceSamplingProduct_bounds stage r b E G k p.1 p.2)

theorem sourceSamplingProduct_mixed_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingProduct stage r b E G n p.1 p.2*sourceSamplingIdealDensity stage r b E G p.2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) :=
  sampling_bounded_product_integrable _ _ _
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    ((sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd) _
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)
    (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_SelfSummability
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- A concrete logarithmic estimate sufficient for the source exponent gap. -/
theorem sampling_self_base_bound (m : ℝ) (hm1 : 1 ≤ m) (hlarge : 802 ≤ m^(1/50 : ℝ)) :
    2+8*m^(3/5 : ℝ)*Real.log m ≤ m^(63/100 : ℝ) := by
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have hl := Real.log_le_rpow_div hm.le (by norm_num : (0 : ℝ) < 1/100)
  have he : m^(3/5 : ℝ)*m^(1/100 : ℝ) = m^(61/100 : ℝ) := by
    rw [← Real.rpow_add hm]; norm_num
  have hpow : 1 ≤ m^(61/100 : ℝ) := Real.one_le_rpow hm1 (by norm_num)
  have hmul : m^(3/5 : ℝ)*Real.log m ≤ 100*m^(61/100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hm.le (3/5 : ℝ))
    rw [← mul_div_assoc,he] at hh
    linarith
  calc
    _ ≤ 802*m^(61/100 : ℝ) := by linarith
    _ ≤ m^(1/50 : ℝ)*m^(61/100 : ℝ) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = _ := by rw [← Real.rpow_add hm]; norm_num

theorem sourceSamplingSelfBudget_eventually : ∀ᶠ stage in atTop,
    sourceSamplingSelfBudget stage ≤ (sourceBlockSize stage : ℝ)^(-(1/25 : ℝ)*(sourceBlockSize stage : ℝ)) := by
  have ht : Tendsto (fun stage => (sourceBlockSize stage : ℝ)^(1/50 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/50)).comp
      (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  filter_upwards [ht.eventually (eventually_ge_atTop 802),sourceSamplingPowers_eventually] with stage hlarge hspec
  let m : ℝ := sourceBlockSize stage
  let B := 2+8*m^(3/5 : ℝ)*Real.log m
  let P : ℝ := (sourceSamplingPowers stage).card
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm1 : 1 ≤ m := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    dsimp [m]; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity [Real.log_nonneg hm1]
  have hB : B ≤ m^(63/100 : ℝ) := sampling_self_base_bound m hm1 hlarge
  have hnum : B^(sourceSamplingPrefix stage).card ≤ m^((65/100 : ℝ)*m) := by
    calc
      _ ≤ (m^(63/100 : ℝ))^(sourceSamplingPrefix stage).card := pow_le_pow_left₀ hB0 hB _
      _ = m^((63/100 : ℝ)*((sourceSamplingPrefix stage).card : ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hm.le]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by
        have hd := sourceSamplingPrefix_card_bound stage
        change ((sourceSamplingPrefix stage).card : ℝ) ≤ (101/100 : ℝ)*m at hd
        nlinarith)
  have hP : m^((69/100 : ℝ)*m) ≤ P := hspec.2.1
  have hPpos : 0 < P := (Real.rpow_pos_of_pos hm _).trans_le hP
  change B^(sourceSamplingPrefix stage).card/P ≤ m^(-(1/25 : ℝ)*m)
  calc
    _ ≤ m^((65/100 : ℝ)*m)/P := div_le_div_of_nonneg_right hnum hPpos.le
    _ ≤ m^((65/100 : ℝ)*m)/m^((69/100 : ℝ)*m) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hP
    _ = _ := by rw [← Real.rpow_sub hm]; congr 1; ring

/-- The actual block growth makes the inverse-square stage sequence summable. -/
theorem sourceSampling_inverse_square_summable : Summable (fun stage => (sourceBlockSize stage : ℝ)^(-2 : ℝ)) := by
  have hg : Summable (fun stage : ℕ => (1/4 : ℝ)^stage) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply hg.of_nonneg_of_le (fun _ => by positivity)
  intro stage
  have hp : (2 : ℝ)^stage ≤ sourceBlockSize stage := by
    have hh := (sourceStage stage).m_ge_pow
    have hle : 2^stage ≤ 2^(stage+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hle.trans hh
  calc
    _ ≤ ((2 : ℝ)^stage)^(-2 : ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) hp (by norm_num)
    _ = _ := by
      rw [Real.rpow_neg (by positivity),Real.rpow_two]
      rw [← pow_mul, Nat.mul_comm stage 2, pow_mul, ← inv_pow]
      norm_num

/-- Summability of the actual full-product self-pair budget. -/
theorem sourceSamplingSelfBudget_summable : Summable sourceSamplingSelfBudget := by
  apply sourceSampling_inverse_square_summable.of_norm_bounded_eventually_nat
  filter_upwards [sourceSamplingSelfBudget_eventually] with stage hb
  have hm : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
  have hn : 0 ≤ sourceSamplingSelfBudget stage := by
    unfold sourceSamplingSelfBudget
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ sourceBlockSize stage by linarith)
    positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_DiagonalContribution
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceSamplingDiagonalContribution_nonneg (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingDiagonalContribution stage r b E G θ :=
  div_nonneg (sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))) (sq_nonneg _)

theorem sourceSamplingProduct_square_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingProduct stage r b E G n p.1 p.2 ^ 2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) :=
  sampling_square_integrable _ _
    ((max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card)
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)

/-- The diagonal contribution's expectation is bounded by the proved
summable budget; the finite set is the actual deterministic sample set. -/
theorem sourceSamplingDiagonalContribution_expectation (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ θ, sourceSamplingDiagonalContribution stage r b E G θ ∂sourceAngleLaw) ≤ sourceSamplingSelfBudget stage := by
  have hP : (0 : ℝ) < (sourceSamplingPowers stage).card :=
    (Real.rpow_pos_of_pos (sourceBlockSize_pos stage) _).trans_le (sourceSamplingPowers_spec stage hs).2.1
  unfold sourceSamplingDiagonalContribution
  rw [integral_div,integral_finsetSum _ (fun n _ =>
    (sourceSamplingProduct_square_integrable stage r b E G hE hG n).integral_prod_left)]
  have hsum := Finset.sum_le_sum (fun n hn => sourceSamplingProduct_self_moment stage hs r b E G hE hG n hn)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  calc
    _ ≤ ((sourceSamplingPowers stage).card : ℝ)*
        (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ))^(sourceSamplingPrefix stage).card /
        ((sourceSamplingPowers stage).card : ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = _ := by unfold sourceSamplingSelfBudget; field_simp

/-- Actual self-pair expectations are summable across the constructed stages. -/
theorem sourceSamplingDiagonalContribution_summable_integral (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Summable (fun stage => ∫ θ, sourceSamplingDiagonalContribution stage r b E G θ ∂sourceAngleLaw) := by
  apply sourceSamplingSelfBudget_summable.of_norm_bounded_eventually_nat
  filter_upwards [sourceBlockSize_tendsto.eventually (eventually_ge_atTop 200000)] with stage hs
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (sourceSamplingDiagonalContribution_nonneg stage r b E G))]
  exact sourceSamplingDiagonalContribution_expectation stage hs r b E G hE hG

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_DiagonalEvent
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Tonelli converts summable expectations of nonnegative functions into
pointwise summability on a conull event. -/
theorem sampling_ae_summable_of_integrals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (f n))
    (hi : ∀ n, Integrable (f n) μ) (hn : ∀ n x, 0 ≤ f n x)
    (hs : Summable (fun n => ∫ x, f n x ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun n => f n x) := by
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f n x) ∂μ) = ENNReal.ofReal (∫ x, f n x ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (hn n))).symm
  have hfin : (∫⁻ x, ∑' n, ENNReal.ofReal (f n x) ∂μ) ≠ ∞ := by
    rw [lintegral_tsum (fun n => (hm n).ennreal_ofReal.aemeasurable)]
    simp_rw [he]
    exact hs.tsum_ofReal_ne_top
  have hm' : Measurable (fun x => ∑' n, ENNReal.ofReal (f n x)) :=
    Measurable.tsum (fun n => (hm n).ennreal_ofReal)
  filter_upwards [ae_lt_top hm' hfin] with x hx
  exact (ENNReal.summable_toReal hx.ne).congr (fun n => ENNReal.toReal_ofReal (hn n x))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_ProductError
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical
noncomputable section

/-- Telescoping products needs upper bounds only. In particular, a zero ideal
coordinate moment causes no division or exceptional case. -/
theorem sampling_product_error {ι : Type*} (S : Finset ι) (f g : ι → ℝ) (M ε : ℝ)
    (hM : 1 ≤ M) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ M) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ M)
    (he : ∀ i ∈ S, |f i-g i| ≤ ε) :
    |(∏ i ∈ S, f i)-(∏ i ∈ S, g i)| ≤ (S.card : ℝ)*ε*M^S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfi := hf i (mem_insert_self _ _)
    have hgi := hg i (mem_insert_self _ _)
    have hei := he i (mem_insert_self _ _)
    have hfS : ∀ j ∈ S, 0 ≤ f j ∧ f j ≤ M := fun j hj => hf j (mem_insert_of_mem hj)
    have hgS : ∀ j ∈ S, 0 ≤ g j ∧ g j ≤ M := fun j hj => hg j (mem_insert_of_mem hj)
    have heS : ∀ j ∈ S, |f j-g j| ≤ ε := fun j hj => he j (mem_insert_of_mem hj)
    have hprod : 0 ≤ ∏ j ∈ S, g j := prod_nonneg (fun j hj => (hgS j hj).1)
    have hprodM : (∏ j ∈ S, g j) ≤ M^S.card := by
      calc
        _ ≤ ∏ _j ∈ S, M := prod_le_prod (fun j hj => (hgS j hj).1) (fun j hj => (hgS j hj).2)
        _ = _ := by simp
    have hMp : 0 ≤ M^S.card := pow_nonneg (by linarith) _
    have hbase : 0 ≤ (S.card : ℝ)*ε*M^S.card := by positivity
    rw [prod_insert hi,prod_insert hi,card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    calc
      _ = |f i*((∏ j ∈ S, f j)-(∏ j ∈ S, g j))+(f i-g i)*(∏ j ∈ S, g j)| := by congr 1; ring
      _ ≤ |f i*((∏ j ∈ S, f j)-(∏ j ∈ S, g j))|+|(f i-g i)*(∏ j ∈ S, g j)| := abs_add_le _ _
      _ = f i*|(∏ j ∈ S, f j)-(∏ j ∈ S, g j)|+|f i-g i| *(∏ j ∈ S, g j) := by
        rw [abs_mul,abs_mul,abs_of_nonneg hfi.1,abs_of_nonneg hprod]
      _ ≤ M*((S.card : ℝ)*ε*M^S.card)+ε*M^S.card := by
        exact add_le_add (mul_le_mul hfi.2 (ih hfS hgS heS) (abs_nonneg _) (by linarith))
          (mul_le_mul hei hprodM hprod hε)
      _ ≤ _ := by nlinarith [mul_nonneg hε hMp,mul_nonneg (show 0 ≤ M-1 by linarith) (mul_nonneg hε hMp)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_ProductError
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- Uniform telescoping budget from the actual ideal coordinate moments. -/
theorem sourceSampling_coordinate_product_error (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (f : SourceCoordinate → ℝ) (hf : ∀ i ∈ sourceSamplingPrefix stage, 0 ≤ f i)
    (he : ∀ i ∈ sourceSamplingPrefix stage,
      |f i-(∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (E i) (G i) s^2 ∂unitIntervalMeasure)| ≤ 104*(sourceBlockSize stage : ℝ)^(-74 : ℝ)) :
    |(∏ i ∈ sourceSamplingPrefix stage, f i)-
      (∫ x, sourceSamplingIdealDensity stage r b E G x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))| ≤ sourceSamplingCorrelationBudget stage := by
  let A (i : SourceCoordinate) := ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i) s^2 ∂unitIntervalMeasure
  let x := (sourceBlockSize stage : ℝ)^(-6/5 : ℝ)
  let ε := 104*(sourceBlockSize stage : ℝ)^(-74 : ℝ)
  let M := 1+108*x
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have h : 100 ≤ sourceBlockSize stage := (sourceStage stage).m_ge_100
    exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεx : ε ≤ 104*x := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (-74 : ℝ) ≤ -6/5)) (by norm_num)
  have hA (i : SourceCoordinate) : 0 ≤ A i ∧ A i ≤ 1+4*x :=
    ⟨integral_nonneg (fun _ => sq_nonneg _),(sourceSampling_oriented_moment stage r (b i) (E i) (G i) (hE i) (hG i)).2⟩
  have hfb (i : SourceCoordinate) (hi : i ∈ sourceSamplingPrefix stage) : 0 ≤ f i ∧ f i ≤ M := by
    refine ⟨hf i hi,?_⟩
    have hh := (abs_le.mp (he i hi)).2
    have ha := (hA i).2
    dsimp [M]
    change f i-A i ≤ ε at hh
    linarith
  have hAb (i : SourceCoordinate) (_hi : i ∈ sourceSamplingPrefix stage) : 0 ≤ A i ∧ A i ≤ M :=
    ⟨(hA i).1,(hA i).2.trans (by dsimp [M]; linarith)⟩
  have hpow : M^(sourceSamplingPrefix stage).card ≤ Real.exp 135 := by
    have hp := product_energy_le_exp (fun _i : sourceSamplingPrefix stage => M)
      (fun _i : sourceSamplingPrefix stage => 108*x)
      (fun _ => by dsimp [M]; positivity) (fun _ => le_rfl)
    have hbudget : ((sourceSamplingPrefix stage).card : ℝ)*(108*x) ≤ 135 := by
      have hh := sourceSampling_prefix_quadratic_budget stage
      change ((sourceSamplingPrefix stage).card : ℝ)*(4*x) ≤ 5 at hh
      nlinarith
    have hp' : M^(sourceSamplingPrefix stage).card ≤
        Real.exp (((sourceSamplingPrefix stage).card : ℝ)*(108*x)) := by simpa using hp
    exact hp'.trans (Real.exp_le_exp.mpr hbudget)
  rw [sourceSamplingIdealDensity_square stage r b E G hE hG]
  apply (sampling_product_error (sourceSamplingPrefix stage) f A M ε (by dsimp [M]; linarith) hε hfb hAb he).trans
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Distinct products under the actual angle and Haar laws. -/
theorem sourceSamplingProduct_pair_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (a c a' c' : SourceCoordinate → ℝ)
    (n k : ℤ) (hn : n ∈ sourceSamplingPowers stage) (hk : k ∈ sourceSamplingPowers stage) (hne : n ≠ k) :
    |(∫ θ, ∫ x, sourceSamplingProduct stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) n θ x *
        sourceSamplingProduct stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) k θ x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw)-
      (∫ x, sourceSamplingIdealDensity stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))| ≤ sourceSamplingCorrelationBudget stage := by
  rw [integral_integral_swap (sourceSamplingProduct_pair_integrable stage r b _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) n k),
    sourceSamplingProduct_inner_factorization stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) n k]
  apply sourceSampling_coordinate_product_error stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  · intro i _
    have hp := sourceSampling_parameters stage
    exact integral_nonneg (fun s => integral_nonneg (fun θ => mul_nonneg
      (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s _).1
      (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s _).1))
  · intro i hi
    have hip : i.1 ≤ stage := by
      have hh := (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mp hi
      omega
    exact sourceSampling_coordinate_pair_error stage hs i hip n k hn hk hne r (b i) (a i) (c i) (a' i) (c' i)

/-- Actual mixed products have the same uniform error budget. -/
theorem sourceSamplingProduct_mixed_error (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    |(∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x*sourceSamplingIdealDensity stage r b E G x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw)-
      (∫ x, sourceSamplingIdealDensity stage r b E G x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))| ≤ sourceSamplingCorrelationBudget stage := by
  rw [integral_integral_swap (sourceSamplingProduct_mixed_integrable stage r b E G hE hG n),
    sourceSamplingProduct_mixed_factorization stage r b E G hE hG n]
  apply sourceSampling_coordinate_product_error stage r b E G hE hG
  · intro i _
    have hp := sourceSampling_parameters stage
    exact integral_nonneg (fun s => mul_nonneg
      (integral_nonneg (fun t => (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s t).1))
      (integral_nonneg (fun θ => (samplingOrientedWeight_bounds r (b i) _ _ _ _ hp.1 hp.2.2 s _).1)))
  · intro i hi
    have hip : i.1 ≤ stage := by
      have hh := (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mp hi
      omega
    apply (sourceSampling_coordinate_mixed_error stage hs i hip n hn r (b i) (E i) (G i) (hE i) (hG i)).trans
    have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
    have he := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (-80 : ℝ) ≤ -74)
    nlinarith [Real.rpow_nonneg (sourceBlockSize_pos stage).le (-74 : ℝ)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Cancellation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical
noncomputable section

/-- Exact finite-average expansion, before bounding or discarding any term. -/
theorem sampling_average_square_expansion {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (hpair : ∀ n ∈ S, ∀ k ∈ S, Integrable (fun x => f n x*f k x) μ)
    (hmix : ∀ n ∈ S, Integrable (fun x => f n x*g x) μ)
    (hg : Integrable (fun x => g x^2) μ) :
    (∫ x, ((∑ n ∈ S, f n x)/(S.card : ℝ)-g x)^2 ∂μ) =
      (∑ n ∈ S, ∑ k ∈ S, ∫ x, f n x*f k x ∂μ)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, ∫ x, f n x*g x ∂μ)/(S.card : ℝ)+(∫ x, g x^2 ∂μ) := by
  have he (x : Ω) : ((∑ n ∈ S, f n x)/(S.card : ℝ)-g x)^2 =
      (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)+g x^2 := by
    have hsq : (∑ n ∈ S, ∑ k ∈ S, f n x*f k x) = (∑ n ∈ S, f n x)^2 := by
      rw [pow_two]; simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [hsq,← Finset.sum_mul]
    ring
  have hpi := integrable_finsetSum S (fun n hn => integrable_finsetSum S (fun k hk => hpair n hn k hk))
  have hmi := integrable_finsetSum S (fun n hn => hmix n hn)
  have hiP : Integrable (fun x => (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2) μ := hpi.div_const _
  have hiM : Integrable (fun x => 2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)) μ := (hmi.const_mul 2).div_const _
  have hiSub : Integrable (fun x => (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)) μ := hiP.sub hiM
  have hpis : (∫ x, ∑ n ∈ S, ∑ k ∈ S, f n x*f k x ∂μ) =
      ∑ n ∈ S, ∑ k ∈ S, ∫ x, f n x*f k x ∂μ := by
    rw [integral_finsetSum S (fun n hn => integrable_finsetSum S (fun k hk => hpair n hn k hk))]
    apply sum_congr rfl
    intro n hn
    exact integral_finsetSum S (fun k hk => hpair n hn k hk)
  simp_rw [he]
  rw [integral_add hiSub hg,integral_sub hiP hiM,integral_div,integral_div,integral_const_mul,
    hpis,integral_finsetSum S (fun n hn => hmix n hn)]

/-- Integrability of the full error follows from the same finite expansion. -/
theorem sampling_average_square_integrable {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (hpair : ∀ n ∈ S, ∀ k ∈ S, Integrable (fun x => f n x*f k x) μ)
    (hmix : ∀ n ∈ S, Integrable (fun x => f n x*g x) μ)
    (hg : Integrable (fun x => g x^2) μ) :
    Integrable (fun x => ((∑ n ∈ S, f n x)/(S.card : ℝ)-g x)^2) μ := by
  have hpi := integrable_finsetSum S (fun n hn => integrable_finsetSum S (fun k hk => hpair n hn k hk))
  have hmi := integrable_finsetSum S (fun n hn => hmix n hn)
  have h : Integrable (fun x => (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)+g x^2) μ :=
    ((hpi.div_const _).sub ((hmi.const_mul 2).div_const _)).add hg
  apply h.congr
  apply Eventually.of_forall
  intro x
  have hsq : (∑ n ∈ S, ∑ k ∈ S, f n x*f k x) = (∑ n ∈ S, f n x)^2 := by
    rw [pow_two]; simp_rw [Finset.sum_mul,Finset.mul_sum]
  dsimp only
  rw [hsq,← Finset.sum_mul]
  ring

/-- The distinct-pair and mixed main terms cancel to -A/P. Since A is
nonnegative, the surviving upper bound is the actual diagonal term plus 3ε. -/
theorem sampling_finite_cancellation {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (B : ι → ι → ℝ) (M : ι → ℝ) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hpair : ∀ n ∈ S, ∀ k ∈ S, n ≠ k → |B n k-A| ≤ ε)
    (hmix : ∀ n ∈ S, |M n-A| ≤ ε) :
    (∑ n ∈ S, ∑ k ∈ S, B n k)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, M n)/(S.card : ℝ)+A ≤
      (∑ n ∈ S, B n n)/(S.card : ℝ)^2+3*ε := by
  let N : ℝ := S.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hS.card_pos
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ S.card from hS.card_pos)
  have hp (n : ι) (hn : n ∈ S) :
      (∑ k ∈ S, B n k) ≤ B n n+(N-1)*(A+ε) := by
    have hoff : (∑ k ∈ S.erase n, B n k) ≤ ((S.erase n).card : ℝ)*(A+ε) := by
      calc
        _ ≤ ∑ _k ∈ S.erase n, (A+ε) := sum_le_sum (fun k hk => by
          have hmem := mem_erase.mp hk
          have hb := (abs_le.mp (hpair n hn k hmem.2 (Ne.symm hmem.1))).2
          linarith)
        _ = _ := by simp; ring
    have hc : ((S.erase n).card : ℝ) = N-1 := by
      rw [card_erase_of_mem hn,Nat.cast_sub (by exact hS.card_pos),Nat.cast_one]
    rw [hc] at hoff
    have he := sum_erase_add S (fun k => B n k) hn
    linarith
  have hpall : (∑ n ∈ S, ∑ k ∈ S, B n k) ≤
      (∑ n ∈ S, B n n)+N*(N-1)*(A+ε) := by
    calc
      _ ≤ ∑ n ∈ S, (B n n+(N-1)*(A+ε)) := sum_le_sum hp
      _ = _ := by rw [sum_add_distrib]; simp [N]; ring
  have hmall : N*(A-ε) ≤ ∑ n ∈ S, M n := by
    calc
      _ = ∑ _n ∈ S, (A-ε) := by simp [N]; ring
      _ ≤ _ := sum_le_sum (fun n hn => by have hh := (abs_le.mp (hmix n hn)).1; linarith)
  change _/N^2-2*_/N+A ≤ _/N^2+3*ε
  have hpdiv := div_le_div_of_nonneg_right hpall (sq_nonneg N)
  have hmdiv := div_le_div_of_nonneg_right hmall hN.le
  have hcancel : ((∑ n ∈ S, B n n)+N*(N-1)*(A+ε))/N^2-
      2*(N*(A-ε))/N+A =
      (∑ n ∈ S, B n n)/N^2+3*ε-(A+ε)/N := by field_simp; ring
  have hnneg : 0 ≤ (A+ε)/N := div_nonneg (add_nonneg hA hε) hN.le
  simp only [mul_div_assoc] at hmdiv hcancel ⊢
  nlinarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Error
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceSampling_error_joint_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      (sourceSamplingEmpiricalDensity stage r b E G p.1 p.2-sourceSamplingIdealDensity stage r b E G p.2)^2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) := by
  apply sampling_average_square_integrable
  · intro n _ k _
    exact sourceSamplingProduct_pair_integrable stage r b E G hE hG n k
  · intro n _
    exact sourceSamplingProduct_mixed_integrable stage r b E G hE hG n
  · have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingIdealDensity stage r b E G p.2) :=
      (sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd
    have hi := sampling_bounded_product_integrable
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)))
      (fun p => sourceSamplingIdealDensity stage r b E G p.2) (fun p => sourceSamplingIdealDensity stage r b E G p.2)
      hm hm _ (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
      (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
    simpa only [pow_two] using hi

theorem sourceSamplingSquaredError_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Integrable (sourceSamplingSquaredError stage r b E G) sourceAngleLaw :=
  (sourceSampling_error_joint_integrable stage r b E G hE hG).integral_prod_left

theorem sourceSamplingSquaredError_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Measurable (sourceSamplingSquaredError stage r b E G) := by
  have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingEmpiricalDensity stage r b E G p.1 p.2) :=
    (Finset.measurable_sum _ (fun n _ => sourceSamplingProduct_measurable stage r b E G hE hG n)).div_const _
  exact ((hm.sub ((sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd)).pow_const 2).stronglyMeasurable.integral_prod_right.measurable

theorem sourceSamplingSquaredError_nonneg (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingSquaredError stage r b E G θ := integral_nonneg (fun _ => sq_nonneg _)

/-- Full expected squared sampling error with the source's actual sample set,
weights and ideal density. All distinct-pair and mixed assumptions are proved. -/
theorem sourceSamplingSquaredError_expectation (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (a c a' c' : SourceCoordinate → ℝ) :
    (∫ θ, sourceSamplingSquaredError stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ ∂sourceAngleLaw) ≤
      (∫ θ, sourceSamplingDiagonalContribution stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ ∂sourceAngleLaw)+
      3*sourceSamplingCorrelationBudget stage := by
  let E := fun i => Set.Icc (a i) (c i)
  let G := fun i => Set.Icc (a' i) (c' i)
  have hE : ∀ i, MeasurableSet (E i) := fun _ => measurableSet_Icc
  have hG : ∀ i, MeasurableSet (G i) := fun _ => measurableSet_Icc
  let μ := sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))
  let S := sourceSamplingPowers stage
  let f (n : ℤ) (p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) := sourceSamplingProduct stage r b E G n p.1 p.2
  let g (p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) := sourceSamplingIdealDensity stage r b E G p.2
  have hpair (n k : ℤ) : Integrable (fun p => f n p*f k p) μ :=
    sourceSamplingProduct_pair_integrable stage r b E G hE hG n k
  have hmix (n : ℤ) : Integrable (fun p => f n p*g p) μ :=
    sourceSamplingProduct_mixed_integrable stage r b E G hE hG n
  have hg : Integrable (fun p => g p^2) μ := by
    have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingIdealDensity stage r b E G p.2) :=
      (sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd
    simpa only [pow_two] using sampling_bounded_product_integrable μ g g hm hm _
      (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
      (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)
  have hA : (∫ p, g p^2 ∂μ) = ∫ x, sourceSamplingIdealDensity stage r b E G x^2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) := by
    rw [integral_prod _ hg]
    simp [g]
  have hB (n k : ℤ) : (∫ p, f n p*f k p ∂μ) =
      ∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x*sourceSamplingProduct stage r b E G k θ x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw := integral_prod _ (hpair n k)
  have hM (n : ℤ) : (∫ p, f n p*g p ∂μ) =
      ∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x*sourceSamplingIdealDensity stage r b E G x
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw := integral_prod _ (hmix n)
  have hS : S.Nonempty := by
    have hP : (0 : ℝ) < (sourceSamplingPowers stage).card :=
      (Real.rpow_pos_of_pos (sourceBlockSize_pos stage) _).trans_le (sourceSamplingPowers_spec stage hs).2.1
    exact Finset.card_pos.mp (by exact_mod_cast hP)
  have hc := sampling_finite_cancellation S hS
    (fun n k => ∫ p, f n p*f k p ∂μ) (fun n => ∫ p, f n p*g p ∂μ)
    (∫ p, g p^2 ∂μ) (sourceSamplingCorrelationBudget stage)
    (integral_nonneg (fun _ => sq_nonneg _)) (by unfold sourceSamplingCorrelationBudget; positivity)
    (fun n hn k hk hne => by rw [hB,hA]; exact sourceSamplingProduct_pair_error stage hs r b a c a' c' n k hn hk hne)
    (fun n hn => by rw [hM,hA]; exact sourceSamplingProduct_mixed_error stage hs r b E G hE hG n hn)
  have hex := sampling_average_square_expansion μ S f g (fun n _ k _ => hpair n k) (fun n _ => hmix n) hg
  rw [← hex] at hc
  have hErr : (∫ p, ((∑ n ∈ S, f n p)/(S.card : ℝ)-g p)^2 ∂μ) =
      ∫ θ, sourceSamplingSquaredError stage r b E G θ ∂sourceAngleLaw :=
    integral_prod _ (sourceSampling_error_joint_integrable stage r b E G hE hG)
  have hDiag : (∑ n ∈ S, ∫ p, f n p*f n p ∂μ)/(S.card : ℝ)^2 =
      ∫ θ, sourceSamplingDiagonalContribution stage r b E G θ ∂sourceAngleLaw := by
    unfold sourceSamplingDiagonalContribution
    rw [integral_div,integral_finsetSum _ (fun n _ =>
      (sourceSamplingProduct_square_integrable stage r b E G hE hG n).integral_prod_left)]
    simp only [hB,pow_two,f,S]
  rw [hErr,hDiag] at hc
  exact hc

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_ErrorEvent
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical Topology
noncomputable section

/-- The distinct and mixed error budget is summable along the actual stages. -/
theorem sourceSamplingCorrelationBudget_summable : Summable sourceSamplingCorrelationBudget := by
  apply (sourceSampling_inverse_square_summable.mul_left (208*Real.exp 135)).of_nonneg_of_le
  · intro stage; unfold sourceSamplingCorrelationBudget; positivity
  intro stage
  let m : ℝ := sourceBlockSize stage
  have hm : 0 < m := sourceBlockSize_pos stage
  have hm1 : 1 ≤ m := by
    have hh : 100 ≤ sourceBlockSize stage := (sourceStage stage).m_ge_100
    dsimp [m]
    exact_mod_cast (show 1 ≤ sourceBlockSize stage by omega)
  have hd : ((sourceSamplingPrefix stage).card : ℝ) ≤ 2*m :=
    (sourceSamplingPrefix_card_bound stage).trans (by dsimp [m]; nlinarith)
  have he : m*m^(-74 : ℝ) = m^(-73 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one m]
    rw [← Real.rpow_add hm]; norm_num
  calc
    sourceSamplingCorrelationBudget stage ≤ (2*m)*(104*m^(-74 : ℝ))*Real.exp 135 := by
      unfold sourceSamplingCorrelationBudget
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity)
    _ = (208*Real.exp 135)*m^(-73 : ℝ) := by rw [← he]; ring
    _ ≤ (208*Real.exp 135)*m^(-2 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)) (by positivity)

/-- Summable expectations for the full empirical sampling error. -/
theorem sourceSamplingSquaredError_summable_integral (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    Summable (fun stage => ∫ θ, sourceSamplingSquaredError stage r b
      (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ ∂sourceAngleLaw) := by
  have hd := sourceSamplingDiagonalContribution_summable_integral r b
    (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i))
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  have hb := hd.add (sourceSamplingCorrelationBudget_summable.mul_left 3)
  apply hb.of_norm_bounded_eventually_nat
  filter_upwards [sourceBlockSize_tendsto.eventually (eventually_ge_atTop 200000)] with stage hs
  rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (sourceSamplingSquaredError_nonneg stage r b _ _))]
  exact sourceSamplingSquaredError_expectation stage hs r b a c a' c'

/-- The full squared sampling error is summable and converges to zero on a
conull set of actual source angles. This is not just the self-pair event. -/
theorem sourceSamplingSquaredError_ae_oai (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw,
      Summable (fun stage => sourceSamplingSquaredError stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) ∧
      Tendsto (fun stage => sourceSamplingSquaredError stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) atTop (𝓝 0) := by
  have he := sampling_ae_summable_of_integrals sourceAngleLaw
    (fun stage θ => sourceSamplingSquaredError stage r b (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ)
    (fun stage => sourceSamplingSquaredError_measurable stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc))
    (fun stage => sourceSamplingSquaredError_integrable stage r b _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc))
    (fun stage θ => sourceSamplingSquaredError_nonneg stage r b _ _ θ)
    (sourceSamplingSquaredError_summable_integral r b a c a' c')
  exact he.mono (fun θ hθ => ⟨hθ,hθ.tendsto_atTop_zero⟩)

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceSamplingSquaredError_ae_oai := @OAI.FiniteFactor.sourceSamplingSquaredError_ae_oai
