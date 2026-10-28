-- Prove2me | solution 1 for OAI.FiniteFactor.sourceSampling_second_pair_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:40:40.061535+00:00
-- url     : https://prove2.me/submissions/7c54ef11-78ab-46d7-864b-592fec0a5804

import Mathlib
import Definitions.Def_OAIQ3Ff000

section
-- module Solutions.OAIQ5_Hy.Compat
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_CrossedProduct_AngleLaw
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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
-- module Solutions.OAIQ5_Hy.FiniteFactor_PeriodizedUniform
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
-- module Solutions.OAIQ5_Hy.FiniteFactor_CrossedProduct_PhaseMarginal
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

theorem unitInterval_middle_compl (b : ℝ) (hb : 0 ≤ b) :
    unitIntervalMeasure (Set.Icc b (1-b))ᶜ ≤ ENNReal.ofReal (2*b) := by
  rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Icc.compl]
  have hsub : (Set.Icc b (1-b))ᶜ ∩ Set.Ico (0 : ℝ) 1 ⊆
      Set.Ico 0 b ∪ Set.Ioc (1-b) 1 := by
    intro x hx
    by_cases hxb : x < b
    · exact Or.inl ⟨hx.2.1,hxb⟩
    · exact Or.inr ⟨by by_contra hh; exact hx.1 ⟨le_of_not_gt hxb, le_of_not_gt hh⟩, hx.2.2.le⟩
  calc
    _ ≤ volume (Set.Ico 0 b ∪ Set.Ioc (1-b) 1) := measure_mono hsub
    _ ≤ volume (Set.Ico (0 : ℝ) b) + volume (Set.Ioc (1-b) 1) := measure_union_le _ _
    _ = ENNReal.ofReal (2*b) := by
      rw [Real.volume_Ico, Real.volume_Ioc]
      simp only [sub_zero, sub_sub_cancel]
      rw [← ENNReal.ofReal_add hb hb]
      congr 1
      ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_OrbitSampling_Powers
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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_Fourier
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Direct integral estimate for a real nonzero frequency on an interval. -/
theorem norm_interval_fourier_le (a b w : ℝ) (hw : w ≠ 0) :
    ‖∫ t in a..b, Complex.exp ((w : ℂ) * Complex.I * t)‖ ≤ 2 / |w| := by
  rw [integral_exp_mul_complex (mul_ne_zero (Complex.ofReal_ne_zero.mpr hw) Complex.I_ne_zero),
    norm_div, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg w)
  calc
    _ ≤ ‖Complex.exp ((w : ℂ) * Complex.I * b)‖ +
        ‖Complex.exp ((w : ℂ) * Complex.I * a)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- The actual normalized angle interval, before reducing phases modulo one. -/
theorem sourceAngle_fourier_le (i : SourceCoordinate) (w : ℝ) (hw : w ≠ 0) :
    ‖∫ t, Complex.exp ((w : ℂ) * Complex.I * t) ∂sourceAngleMarginal i‖ ≤
      2 / (sourceAngleUnit i * |w|) := by
  have ha := sourceAngleUnit_pos i
  rw [sourceAngleMarginal, sourceAngleInterval, cond_closed_interval_eq,
    ProbabilityTheory.cond, integral_smul_measure, Real.volume_Ioc]
  rw [show 2 * sourceAngleUnit i - sourceAngleUnit i = sourceAngleUnit i by ring]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal ha.le, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  rw [← intervalIntegral.integral_of_le (show sourceAngleUnit i ≤ 2*sourceAngleUnit i by linarith)]
  calc
    _ ≤ (sourceAngleUnit i)⁻¹ * (2 / |w|) :=
      mul_le_mul_of_nonneg_left (norm_interval_fourier_le _ _ w hw) (inv_nonneg.mpr ha.le)
    _ = _ := by ring

/-- Integer frequencies do not see the integer part of a phase. -/
theorem fourier_fract (v : ℤ) (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((v : ℂ) * (Int.fract t : ℝ))) =
      Complex.exp (2 * Real.pi * Complex.I * ((v : ℂ) * (t : ℂ))) := by
  rw [Int.fract]
  push_cast
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((v : ℂ) * ((t : ℂ) - (⌊t⌋ : ℂ))) =
      2 * Real.pi * Complex.I * ((v : ℂ) * (t : ℂ)) +
        ((-(v * ⌊t⌋) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The two actual phases have the Fourier transform of the combined frequency. -/
theorem pair_fourier_fract (v v' : ℤ) (n n' t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract (n*t) : ℝ) + (v' : ℂ) * (Int.fract (n'*t) : ℝ))) =
    Complex.exp (((2 * Real.pi * ((v : ℝ)*n + (v' : ℝ)*n') : ℝ) : ℂ) * Complex.I * t) := by
  rw [mul_add, Complex.exp_add, fourier_fract, fourier_fract, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem sourceAngle_pair_fourier_le (i : SourceCoordinate) (v v' : ℤ) (n n' : ℝ)
    (hw : (v : ℝ)*n + (v' : ℝ)*n' ≠ 0) :
    ‖∫ t, Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract (n*t) : ℝ) + (v' : ℂ) * (Int.fract (n'*t) : ℝ)))
      ∂sourceAngleMarginal i‖ ≤
      1 / (Real.pi * sourceAngleUnit i * |(v : ℝ)*n + (v' : ℝ)*n'|) := by
  simp_rw [pair_fourier_fract]
  have hp := sourceAngle_fourier_le i (2*Real.pi*((v : ℝ)*n+(v' : ℝ)*n'))
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw)
  convert hp using 1
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_OrbitSampling_Fourier
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

/-- The full infinite-product angle expectation has the same coordinate
Fourier estimate; no independence between two phases is asserted. -/
theorem sourceAngleLaw_pair_fourier_le (i : SourceCoordinate) (v v' : ℤ) (n n' : ℝ)
    (hw : (v : ℝ)*n+(v' : ℝ)*n' ≠ 0) :
    ‖∫ θ, Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract (n*θ i) : ℝ) + (v' : ℂ) * (Int.fract (n'*θ i) : ℝ)))
      ∂sourceAngleLaw‖ ≤
      1/(Real.pi*sourceAngleUnit i*|(v : ℝ)*n+(v' : ℝ)*n'|) := by
  have hh := sourceAngle_pair_fourier_le i v v' n n' hw
  simp_rw [pair_fourier_fract] at hh ⊢
  rw [← sourceAngleLaw_coordinate i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)] at hh
  exact hh

theorem sourceSampling_pair_fourier_bound (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers s) (hn' : n' ∈ sourceSamplingPowers s) (hne : n ≠ n')
    (v v' : ℤ) (hv : |v| ≤ (samplingH (sourceBlockSize s) : ℤ))
    (hv' : |v'| ≤ (samplingH (sourceBlockSize s) : ℤ)) (hvv' : v ≠ 0 ∨ v' ≠ 0) :
    ‖∫ θ, Complex.exp (2 * Real.pi * Complex.I *
      ((v : ℂ) * (Int.fract ((n : ℝ)*θ i) : ℝ) +
       (v' : ℂ) * (Int.fract ((n' : ℝ)*θ i) : ℝ))) ∂sourceAngleLaw‖ ≤
      Real.pi⁻¹*(sourceBlockSize s : ℝ)^(-1000 : ℝ) := by
  have hsep := (sourceSamplingPowers_spec s hs).2.2 hn hn' hne
  have hfreq : (samplingR (sourceBlockSize s) (sourceStageState s).K : ℤ) < |v*n+v'*n'| := by
    by_contra hh
    exact hsep ⟨v,mem_Icc.mpr (abs_le.mp hv),v',mem_Icc.mpr (abs_le.mp hv'),hvv',le_of_not_gt hh⟩
  let w : ℝ := (v : ℝ)*(n : ℝ)+(v' : ℝ)*(n' : ℝ)
  have hwR : (samplingR (sourceBlockSize s) (sourceStageState s).K : ℝ) < |w| := by
    dsimp [w]
    exact_mod_cast hfreq
  have hwpos : 0 < |w| := lt_of_le_of_lt (Nat.cast_nonneg _) hwR
  have hw : w ≠ 0 := abs_pos.mp hwpos
  apply (sourceAngleLaw_pair_fourier_le i v v' (n : ℝ) (n' : ℝ) hw).trans
  have hN : (sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K ≤
      (sourceBlockSize s : ℝ)*(sourceStageState s).K := by
    exact_mod_cast sourceFrequencyScale_monotone hi
  have hmpos := sourceBlockSize_pos s
  have hNpos := mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)
  have hscale : (sourceBlockSize s : ℝ)^1000 ≤ sourceAngleUnit i * |w| := by
    unfold samplingR at hwR
    push_cast at hwR
    unfold sourceAngleUnit
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hNpos]
    have hh := mul_le_mul_of_nonneg_right hN (pow_nonneg hmpos.le 1000)
    nlinarith
  change 1/(Real.pi*sourceAngleUnit i*|w|) ≤ _
  calc
    _ = Real.pi⁻¹*(1/(sourceAngleUnit i*|w|)) := by ring
    _ ≤ Real.pi⁻¹*(1/(sourceBlockSize s : ℝ)^1000) := by
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (pow_pos hmpos 1000) hscale) (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by rw [Real.rpow_neg, Real.rpow_ofNat, one_div]; positivity

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_Periodization
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_Kernel
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ComplexConjugate
noncomputable section

theorem samplingCharacter_norm (v : ℤ) (t : ℝ) : ‖samplingCharacter v t‖ = 1 := by
  simp [samplingCharacter, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem samplingCharacter_continuous (v : ℤ) : Continuous (samplingCharacter v) := by
  unfold samplingCharacter
  fun_prop

theorem samplingCharacter_zero (t : ℝ) : samplingCharacter 0 t = 1 := by simp [samplingCharacter]

theorem samplingCharacter_add (v w : ℤ) (t : ℝ) :
    samplingCharacter (v+w) t = samplingCharacter v t * samplingCharacter w t := by
  unfold samplingCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem samplingCharacter_neg (v : ℤ) (t : ℝ) :
    samplingCharacter (-v) t = conj (samplingCharacter v t) := by
  have htwo : conj (2 : ℂ) = 2 := by
    change conj ((2 : ℝ) : ℂ) = _
    exact Complex.conj_ofReal _
  simp [samplingCharacter, ← Complex.exp_conj, mul_assoc, htwo]

theorem samplingCharacter_sub (v w : ℤ) (t : ℝ) :
    samplingCharacter (v-w) t = samplingCharacter v t * conj (samplingCharacter w t) := by
  rw [sub_eq_add_neg, samplingCharacter_add, samplingCharacter_neg]

theorem samplingCharacter_integrable (v : ℤ) :
    Integrable (samplingCharacter v) unitIntervalMeasure :=
  (samplingCharacter_continuous v).integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

theorem samplingCharacter_integral (v : ℤ) :
    (∫ t, samplingCharacter v t ∂unitIntervalMeasure) = if v = 0 then 1 else 0 := by
  by_cases hv : v = 0
  · subst v; simp [samplingCharacter_zero]
  rw [ite_eq_right hv]
  unfold unitIntervalMeasure
  rw [restrict_Ico_eq_restrict_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ t in (0 : ℝ)..1, Complex.exp ((2 * Real.pi * Complex.I * (v : ℂ)) * t)) = 0
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have hcoef : 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) hvC
  rw [integral_exp_mul_complex hcoef]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) = (v : ℂ)*(2*Real.pi*Complex.I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem samplingKernel_nonneg (H : ℕ) (t : ℝ) : 0 ≤ samplingKernel H t := by
  unfold samplingKernel
  positivity

theorem samplingKernel_continuous (H : ℕ) : Continuous (samplingKernel H) := by
  unfold samplingKernel
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  exact continuous_finsetSum _ (fun r _ => samplingCharacter_continuous _)

theorem samplingKernel_expansion (H : ℕ) (t : ℝ) :
    (samplingKernel H t : ℂ) = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ q ∈ Finset.range H, samplingCharacter ((r : ℤ)-(q : ℤ)) t := by
  simp only [samplingKernel, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast,
    samplingCharacter_sub, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.mul_conj]
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_KernelTail
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
noncomputable section

theorem samplingCharacter_nat (r : ℕ) (t : ℝ) :
    samplingCharacter (r : ℤ) t = samplingCharacter 1 t ^ r := by
  induction r with
  | zero => simp [samplingCharacter_zero]
  | succ r ih =>
    rw [Nat.cast_add, Nat.cast_one, samplingCharacter_add, ih, pow_succ]

/-- Geometric-sum cancellation controls the kernel away from the origin. -/
theorem samplingKernel_geometric_bound (H : ℕ) (t : ℝ) :
    ‖∑ r ∈ Finset.range H, samplingCharacter (r : ℤ) t‖ *
      ‖samplingCharacter 1 t - 1‖ ≤ 2 := by
  simp_rw [samplingCharacter_nat]
  rw [← norm_mul, geom_sum_mul]
  calc
    _ ≤ ‖samplingCharacter 1 t ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = _ := by norm_num [norm_pow, samplingCharacter_norm]

/-- Elementary chord lower bound, including both halves of the unit interval. -/
theorem samplingCharacter_chord_lower (δ t : ℝ) (hδ : 0 ≤ δ)
    (ht : δ ≤ t) (ht' : t ≤ 1-δ) :
    4*δ ≤ ‖samplingCharacter 1 t-1‖ := by
  have he : samplingCharacter 1 t = Complex.exp (Complex.I * ((2*Real.pi*t : ℝ) : ℂ)) := by
    unfold samplingCharacter
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have harg : 2*Real.pi*t/2 = Real.pi*t := by ring
  rw [harg, Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  have hsin : 2*δ ≤ Real.sin (Real.pi*t) := by
    by_cases hhalf : t ≤ 1/2
    · have ht0 : 0 ≤ t := hδ.trans ht
      have hh := Real.mul_le_sin (x := Real.pi*t) (by positivity)
        (by nlinarith [Real.pi_pos])
      have he : 2/Real.pi*(Real.pi*t) = 2*t := by field_simp
      rw [he] at hh
      linarith
    · have ht0 : 0 ≤ 1-t := by linarith
      have hh := Real.mul_le_sin (x := Real.pi*(1-t)) (by positivity)
        (by nlinarith [Real.pi_pos])
      have he : 2/Real.pi*(Real.pi*(1-t)) = 2*(1-t) := by field_simp
      rw [he, show Real.pi*(1-t) = Real.pi-Real.pi*t by ring, Real.sin_pi_sub] at hh
      linarith
  have := le_abs_self (Real.sin (Real.pi*t))
  linarith

theorem samplingKernel_tail_bound (H : ℕ) (hH : 0 < H) (δ t : ℝ)
    (hδ : 0 < δ) (ht : δ ≤ t) (ht' : t ≤ 1-δ) :
    samplingKernel H t ≤ 1/(4*(H : ℝ)*δ^2) := by
  have hc := samplingCharacter_chord_lower δ t hδ.le ht ht'
  have hg := samplingKernel_geometric_bound H t
  let A := ‖∑ r ∈ Finset.range H, samplingCharacter (r : ℤ) t‖
  have hA : 0 ≤ A := norm_nonneg _
  have hbound : A ≤ 1/(2*δ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*δ)).mpr
    have hh := mul_le_mul_of_nonneg_left hc hA
    dsimp [A] at *
    nlinarith
  have hsq := pow_le_pow_left₀ hA hbound 2
  have hHR : 0 < (H : ℝ) := by exact_mod_cast hH
  unfold samplingKernel
  calc
    _ ≤ (1/(2*δ))^2/(H : ℝ) := div_le_div_of_nonneg_right hsq hHR.le
    _ = _ := by ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_Smoothing
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ComplexConjugate ENNReal
noncomputable section

theorem samplingCharacter_sub_argument (v : ℤ) (t u : ℝ) :
    samplingCharacter v (t-u) = samplingCharacter v t * samplingCharacter (-v) u := by
  unfold samplingCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem samplingCharacter_fract (v : ℤ) (t : ℝ) :
    samplingCharacter v (Int.fract t) = samplingCharacter v t := by
  simpa only [samplingCharacter, mul_assoc] using fourier_fract v t

theorem samplingKernel_fract (H : ℕ) (t : ℝ) :
    samplingKernel H (Int.fract t) = samplingKernel H t := by
  simp only [samplingKernel, samplingCharacter_fract]

theorem samplingKernel_shift_integral (H : ℕ) (hH : 0 < H) (t : ℝ) :
    (∫ u, samplingKernel H (t-u) ∂unitIntervalMeasure) = 1 := by
  have hc : (∫ u, (samplingKernel H (t-u) : ℂ) ∂unitIntervalMeasure) = 1 := by
    simp_rw [samplingKernel_expansion, samplingCharacter_sub_argument]
    rw [integral_const_mul, integral_finsetSum _ (fun r _ =>
      integrable_finsetSum _ (fun q _ => (samplingCharacter_integrable _).const_mul _))]
    simp_rw [integral_finsetSum _ (fun q _ => (samplingCharacter_integrable _).const_mul _),
      integral_const_mul, samplingCharacter_integral]
    simp [sub_eq_zero, -Finset.mem_range, hH.ne', samplingCharacter_zero]
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

theorem samplingSmooth_bounds (H : ℕ) (hH : 0 < H) (E : Set ℝ) (t : ℝ) :
    0 ≤ samplingSmooth H E t ∧ samplingSmooth H E t ≤ 1 := by
  have hki : Integrable (fun u => samplingKernel H (t-u)) unitIntervalMeasure :=
    ((samplingKernel_continuous H).comp (continuous_const.sub continuous_id)).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  constructor
  · exact integral_nonneg (fun u => samplingKernel_nonneg H (t-u))
  · calc
      _ ≤ ∫ u, samplingKernel H (t-u) ∂unitIntervalMeasure :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (fun u => samplingKernel_nonneg H (t-u))) hki
      _ = 1 := samplingKernel_shift_integral H hH t

theorem samplingIntervalCoefficient_zero (E : Set ℝ) :
    samplingIntervalCoefficient E 0 = ((unitIntervalMeasure E).toReal : ℂ) := by
  simp [samplingIntervalCoefficient, samplingCharacter_zero, measureReal_def]

theorem samplingIntervalCoefficient_norm (E : Set ℝ) (v : ℤ) :
    ‖samplingIntervalCoefficient E v‖ ≤ 1 := by
  unfold samplingIntervalCoefficient
  calc
    _ ≤ ∫ u in E, ‖samplingCharacter (-v) u‖ ∂unitIntervalMeasure := norm_integral_le_integral_norm _
    _ = (unitIntervalMeasure E).toReal := by simp [samplingCharacter_norm, measureReal_def]
    _ ≤ 1 := by
      have hh : unitIntervalMeasure E ≤ 1 :=
        (measure_mono (Set.subset_univ E)).trans_eq (measure_univ)
      simpa using ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hh

/-- An actual finite Fourier expansion of the smoothed interval indicator.
Keeping the two kernel indices avoids assuming a coefficient formula. -/
theorem samplingSmooth_expansion (H : ℕ) (E : Set ℝ) (t : ℝ) :
    (samplingSmooth H E t : ℂ) = (H : ℂ)⁻¹ *
      ∑ r ∈ Finset.range H, ∑ q ∈ Finset.range H,
        samplingCharacter ((r : ℤ)-(q : ℤ)) t *
          samplingIntervalCoefficient E ((r : ℤ)-(q : ℤ)) := by
  rw [samplingSmooth, ← integral_complex_ofReal]
  simp_rw [samplingKernel_expansion, samplingCharacter_sub_argument]
  rw [integral_const_mul, integral_finsetSum _ (fun r _ =>
    integrable_finsetSum _ (fun q _ => ((samplingCharacter_integrable _).restrict).const_mul _))]
  simp_rw [integral_finsetSum _ (fun q _ => ((samplingCharacter_integrable _).restrict).const_mul _),
    integral_const_mul]
  rfl

theorem samplingSmooth_continuous (H : ℕ) (E : Set ℝ) : Continuous (samplingSmooth H E) := by
  have hc : Continuous (fun t => (samplingSmooth H E t : ℂ)) := by
    simp_rw [samplingSmooth_expansion]
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro r hr
    apply continuous_finsetSum
    intro q hq
    exact (samplingCharacter_continuous _).mul_const _
  simpa only [Function.comp_def, Complex.ofReal_re] using Complex.continuous_re.comp hc

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_FourierSum
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
noncomputable section

/-- Bounded characters are integrable under every probability law. -/
theorem samplingCharacter_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (v w : ℤ) :
    Integrable (fun θ => samplingCharacter v (X θ)*samplingCharacter w (Y θ)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((samplingCharacter_continuous v).measurable.comp hX).mul
      ((samplingCharacter_continuous w).measurable.comp hY)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun θ => by simp [samplingCharacter_norm])

/-- Finite Fourier polynomials require only Fourier bounds on the actual
joint law; the two input phases need not be independent. -/
theorem samplingFourier_sum_error {Ω α β : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (F : Finset α) (G : Finset β) (v : α → ℤ) (w : β → ℤ)
    (A : α → ℂ) (B : β → ℂ)
    (hA : ∀ a ∈ F, ‖A a‖ ≤ 1) (hB : ∀ b ∈ G, ‖B b‖ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hFourier : ∀ a ∈ F, ∀ b ∈ G, v a ≠ 0 ∨ w b ≠ 0 →
      ‖∫ θ, samplingCharacter (v a) (X θ)*samplingCharacter (w b) (Y θ) ∂μ‖ ≤ ε) :
    ‖(∫ θ, (∑ a ∈ F, A a*samplingCharacter (v a) (X θ)) *
          (∑ b ∈ G, B b*samplingCharacter (w b) (Y θ)) ∂μ) -
      (∑ a ∈ F, if v a = 0 then A a else 0) *
      (∑ b ∈ G, if w b = 0 then B b else 0)‖ ≤
        (F.card : ℝ)*(G.card : ℝ)*ε := by
  classical
  let τ := fun a b => ∫ θ, samplingCharacter (v a) (X θ)*samplingCharacter (w b) (Y θ) ∂μ
  let d := fun a b => if v a = 0 ∧ w b = 0 then (1 : ℂ) else 0
  have heq (a : α) (b : β) (θ : Ω) :
      (A a*samplingCharacter (v a) (X θ))*(B b*samplingCharacter (w b) (Y θ)) =
      (A a*B b)*(samplingCharacter (v a) (X θ)*samplingCharacter (w b) (Y θ)) := by ring
  have hi (a : α) (b : β) := (samplingCharacter_product_integrable μ X Y hX hY (v a) (w b)).const_mul (A a*B b)
  have hmain : (∫ θ, (∑ a ∈ F, A a*samplingCharacter (v a) (X θ)) *
      (∑ b ∈ G, B b*samplingCharacter (w b) (Y θ)) ∂μ) =
      ∑ a ∈ F, ∑ b ∈ G, A a*B b*τ a b := by
    simp_rw [sum_mul_sum, heq]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
    simp_rw [integral_finsetSum _ (fun b _ => hi _ b), integral_const_mul]
    rfl
  have hconstant : (∑ a ∈ F, if v a = 0 then A a else 0) *
      (∑ b ∈ G, if w b = 0 then B b else 0) =
      ∑ a ∈ F, ∑ b ∈ G, A a*B b*d a b := by
    rw [sum_mul_sum]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    dsimp [d]
    split_ifs <;> simp_all
  have hτ (a : α) (ha : a ∈ F) (b : β) (hb : b ∈ G) : ‖τ a b-d a b‖ ≤ ε := by
    by_cases hz : v a = 0 ∧ w b = 0
    · simpa [τ,d,hz.1,hz.2,samplingCharacter_zero] using hε
    · have hn : v a ≠ 0 ∨ w b ≠ 0 := by tauto
      simpa [τ,d,hz] using hFourier a ha b hb hn
  rw [hmain,hconstant, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ a ∈ F, ‖∑ b ∈ G, A a*B b*(τ a b-d a b)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ F, ∑ b ∈ G, ‖A a*B b*(τ a b-d a b)‖ :=
      sum_le_sum fun a ha => norm_sum_le _ _
    _ ≤ ∑ _a ∈ F, ∑ _b ∈ G, ε := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [norm_mul,norm_mul]
      calc
        _ ≤ 1*1*ε := by gcongr; exact hA a ha; exact hB b hb; exact hτ a ha b hb
        _ = ε := by ring
    _ = _ := by simp; ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SmoothedPair
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
noncomputable section

/-- The finite kernel index form, with total coefficient absolute sum at most H. -/
theorem samplingSmooth_index_expansion (H : ℕ) (E : Set ℝ) (t : ℝ) :
    (samplingSmooth H E t : ℂ) = (H : ℂ)⁻¹ *
      ∑ p ∈ (Finset.range H).product (Finset.range H),
        samplingIntervalCoefficient E ((p.1 : ℤ)-(p.2 : ℤ)) *
          samplingCharacter ((p.1 : ℤ)-(p.2 : ℤ)) t := by
  rw [samplingSmooth_expansion, Finset.product_eq_sprod, sum_product]
  congr 1
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro q hq
  exact mul_comm _ _

theorem samplingSmooth_constant_sum (H : ℕ) (E : Set ℝ) :
    (∑ p ∈ (Finset.range H).product (Finset.range H),
      if (p.1 : ℤ)-(p.2 : ℤ) = 0 then
        samplingIntervalCoefficient E ((p.1 : ℤ)-(p.2 : ℤ)) else 0) =
      (H : ℂ)*((unitIntervalMeasure E).toReal : ℂ) := by
  simp [sum_product, sub_eq_zero, -Finset.mem_range, samplingIntervalCoefficient_zero]

/-- Quantitative smoothed rectangle estimate, with the actual joint Fourier
bound as the only dependence assumption. -/
theorem samplingSmooth_pair_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (H : ℕ) (hH : 0 < H)
    (E E' : Set ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hFourier : ∀ v w : ℤ, |v| < (H : ℤ) → |w| < (H : ℤ) →
      (v ≠ 0 ∨ w ≠ 0) →
      ‖∫ θ, samplingCharacter v (X θ)*samplingCharacter w (Y θ) ∂μ‖ ≤ ε) :
    ‖(∫ θ, (samplingSmooth H E (X θ) : ℂ)*(samplingSmooth H E' (Y θ) : ℂ) ∂μ) -
      ((unitIntervalMeasure E).toReal : ℂ)*((unitIntervalMeasure E').toReal : ℂ)‖ ≤
      (H : ℝ)^2*ε := by
  let F := (Finset.range H).product (Finset.range H)
  let v := fun p : ℕ × ℕ => (p.1 : ℤ)-(p.2 : ℤ)
  let A := fun p => samplingIntervalCoefficient E (v p)
  let B := fun p => samplingIntervalCoefficient E' (v p)
  let P := fun t => ∑ p ∈ F, A p*samplingCharacter (v p) t
  let Q := fun t => ∑ p ∈ F, B p*samplingCharacter (v p) t
  have hfreq (p : ℕ × ℕ) (hp : p ∈ F) : |v p| < (H : ℤ) := by
    obtain ⟨hp,hq⟩ := mem_product.mp hp
    have hp' := mem_range.mp hp
    have hq' := mem_range.mp hq
    dsimp [v]
    rw [abs_lt]
    constructor <;> omega
  have hh := samplingFourier_sum_error μ X Y hX hY F F v v A B
    (fun p hp => samplingIntervalCoefficient_norm E (v p))
    (fun p hp => samplingIntervalCoefficient_norm E' (v p)) ε hε
    (fun p hp q hq hn => hFourier (v p) (v q) (hfreq p hp) (hfreq q hq) hn)
  have ha : (∑ p ∈ F, if v p = 0 then A p else 0) =
      (H : ℂ)*((unitIntervalMeasure E).toReal : ℂ) := samplingSmooth_constant_sum H E
  have hb : (∑ p ∈ F, if v p = 0 then B p else 0) =
      (H : ℂ)*((unitIntervalMeasure E').toReal : ℂ) := samplingSmooth_constant_sum H E'
  rw [ha,hb] at hh
  change ‖(∫ θ, P (X θ)*Q (Y θ) ∂μ) - _‖ ≤ _ at hh
  have hmain : (∫ θ, (samplingSmooth H E (X θ) : ℂ)*(samplingSmooth H E' (Y θ) : ℂ) ∂μ) =
      (H : ℂ)⁻¹^2 * ∫ θ, P (X θ)*Q (Y θ) ∂μ := by
    simp_rw [samplingSmooth_index_expansion]
    change (∫ θ, ((H : ℂ)⁻¹*P (X θ))*((H : ℂ)⁻¹*Q (Y θ)) ∂μ) = _
    have he (θ : Ω) : ((H : ℂ)⁻¹*P (X θ))*((H : ℂ)⁻¹*Q (Y θ)) =
        (H : ℂ)⁻¹^2*(P (X θ)*Q (Y θ)) := by ring
    simp_rw [he]
    exact integral_const_mul _ _
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hz : (H : ℂ)⁻¹^2*((H : ℂ)*((unitIntervalMeasure E).toReal : ℂ)*
      ((H : ℂ)*((unitIntervalMeasure E').toReal : ℂ))) =
      ((unitIntervalMeasure E).toReal : ℂ)*((unitIntervalMeasure E').toReal : ℂ) := by
    field_simp
  rw [hmain, ← hz, ← mul_sub, norm_mul]
  calc
    _ ≤ ‖(H : ℂ)⁻¹^2‖*((F.card : ℝ)*(F.card : ℝ)*ε) :=
      mul_le_mul_of_nonneg_left hh (norm_nonneg _)
    _ = _ := by
      simp only [F, Finset.product_eq_sprod, card_product, card_range, Nat.cast_mul, norm_pow, norm_inv, Complex.norm_natCast]
      field_simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_IntervalError
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- Interval membership cannot change under a displacement smaller than
delta when the starting point is farther than delta from both endpoints. -/
theorem interval_membership_stable (a b δ t u : ℝ) (_hδ : 0 ≤ δ)
    (ha : δ < |t-a|) (hb : δ < |t-b|) (htu : |t-u| < δ) :
    u ∈ Set.Icc a b ↔ t ∈ Set.Icc a b := by
  have hd := abs_lt.mp htu
  constructor
  · intro hu
    constructor
    · by_contra ht
      have hh : t-a < 0 := by linarith
      rw [abs_of_neg hh] at ha
      linarith [hu.1]
    · by_contra ht
      have hh : 0 < t-b := by linarith
      rw [abs_of_pos hh] at hb
      linarith [hu.2]
  · intro ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)] at ha
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at hb
    constructor <;> linarith

/-- A separated pair of representatives, with the first away from the cut,
has a fractional displacement outside the kernel's exceptional arc. -/
theorem fract_displacement_middle (δ t u : ℝ) (hδ : 0 < δ)
    (ht : δ ≤ t) (ht' : t ≤ 1-δ) (hu : u ∈ Set.Ico (0 : ℝ) 1)
    (hsep : δ ≤ |t-u|) : Int.fract (t-u) ∈ Set.Icc δ (1-δ) := by
  by_cases hpos : 0 ≤ t-u
  · rw [abs_of_nonneg hpos] at hsep
    rw [Int.fract_eq_self.mpr ⟨hpos, by linarith [hu.1]⟩]
    constructor <;> linarith [hu.1]
  · have hneg : t-u < 0 := lt_of_not_ge hpos
    rw [abs_of_neg hneg] at hsep
    have hf : ⌊t-u⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith [hu.2], by norm_num; linarith⟩
    rw [Int.fract, hf]
    norm_num
    constructor <;> linarith [hu.2]

/-- The actual interval convolution differs from its indicator only by
the proved kernel tail, away from interval endpoints and the circle cut. -/
theorem samplingSmooth_interval_error (H : ℕ) (hH : 0 < H) (a b δ t : ℝ)
    (hδ : 0 < δ) (ht : δ ≤ t) (ht' : t ≤ 1-δ)
    (ha : δ < |t-a|) (hb : δ < |t-b|) :
    |samplingSmooth H (Set.Icc a b) t - (Set.Icc a b).indicator (fun _ => (1 : ℝ)) t| ≤
      1/(4*(H : ℝ)*δ^2) := by
  let E := Set.Icc a b
  let K := fun u => samplingKernel H (t-u)
  let C := 1/(4*(H : ℝ)*δ^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hki : Integrable K unitIntervalMeasure :=
    ((samplingKernel_continuous H).comp (continuous_const.sub continuous_id)).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  have hcut (B : Set ℝ) (hBm : MeasurableSet B)
      (hB : ∀ u ∈ B, ¬(u ∈ E ↔ t ∈ E)) :
      (∫ u in B, K u ∂unitIntervalMeasure) ≤ C := by
    rw [← integral_indicator hBm]
    have hle : ∀ᵐ u ∂unitIntervalMeasure, B.indicator K u ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
      by_cases hub : u ∈ B
      · rw [Set.indicator_of_mem hub]
        have hsep : δ ≤ |t-u| := by
          by_contra hh
          exact hB u hub (interval_membership_stable a b δ t u hδ.le ha hb (lt_of_not_ge hh))
        have hf := fract_displacement_middle δ t u hδ ht ht' hu hsep
        dsimp [K,C]
        rw [← samplingKernel_fract H (t-u)]
        exact samplingKernel_tail_bound H hH δ _ hδ hf.1 hf.2
      · rw [Set.indicator_of_notMem hub]
        exact hC
    have hh := integral_mono_ae (hki.indicator hBm) (integrable_const C) hle
    simpa using hh
  have hbounds := samplingSmooth_bounds H hH E t
  by_cases hte : t ∈ E
  · rw [Set.indicator_of_mem hte, abs_of_nonpos (by linarith [hbounds.2])]
    have hh := hcut Eᶜ measurableSet_Icc.compl (fun u hu he => hu (he.mpr hte))
    have hsplit := integral_add_compl (s := E) measurableSet_Icc hki
    have hone : (∫ u, K u ∂unitIntervalMeasure) = 1 := samplingKernel_shift_integral H hH t
    change (∫ u in E, K u ∂unitIntervalMeasure) + (∫ u in Eᶜ, K u ∂unitIntervalMeasure) = _ at hsplit
    change -(samplingSmooth H E t-1) ≤ C
    have heq : (∫ u in E, K u ∂unitIntervalMeasure) = samplingSmooth H E t := rfl
    rw [hone,heq] at hsplit
    linarith
  · rw [Set.indicator_of_notMem hte, sub_zero, abs_of_nonneg hbounds.1]
    exact hcut E measurableSet_Icc (fun u hu he => hte (he.mp hu))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SmoothingLaw
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

theorem samplingBoundary_measurable (a b δ : ℝ) : MeasurableSet (samplingBoundary a b δ) :=
  (measurableSet_Icc.compl.union measurableSet_Icc).union measurableSet_Icc

theorem samplingBoundary_measure (a b δ : ℝ) (hδ : 0 ≤ δ) :
    unitIntervalMeasure (samplingBoundary a b δ) ≤ ENNReal.ofReal (6*δ) := by
  have hband (a : ℝ) : unitIntervalMeasure (Set.Icc (a-δ) (a+δ)) ≤ ENNReal.ofReal (2*δ) := by
    calc
      _ ≤ volume (Set.Icc (a-δ) (a+δ)) := Measure.restrict_le_self _
      _ = _ := by rw [Real.volume_Icc]; congr 1; ring
  calc
    _ ≤ unitIntervalMeasure ((Set.Icc δ (1-δ))ᶜ ∪ Set.Icc (a-δ) (a+δ)) +
        unitIntervalMeasure (Set.Icc (b-δ) (b+δ)) := measure_union_le _ _
    _ ≤ unitIntervalMeasure (Set.Icc δ (1-δ))ᶜ +
        unitIntervalMeasure (Set.Icc (a-δ) (a+δ)) +
        unitIntervalMeasure (Set.Icc (b-δ) (b+δ)) := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (2*δ) + ENNReal.ofReal (2*δ) + ENNReal.ofReal (2*δ) := by
      gcongr
      · exact unitInterval_middle_compl δ hδ
      · exact hband a
      · exact hband b
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

theorem samplingSmooth_indicator_error_le_one (H : ℕ) (hH : 0 < H) (E : Set ℝ) (t : ℝ) :
    |samplingSmooth H E t - E.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
  have h := samplingSmooth_bounds H hH E t
  by_cases ht : t ∈ E
  · rw [Set.indicator_of_mem ht]
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · rw [Set.indicator_of_notMem ht, sub_zero, abs_of_nonneg h.1]
    exact h.2

/-- The interval smoothing error integrated under any actual phase law with
density bounded by two. Only one-dimensional domination is used. -/
theorem samplingSmooth_expected_error (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν ≤ (2 : ℝ≥0∞) • unitIntervalMeasure) (H : ℕ) (hH : 0 < H)
    (a b δ : ℝ) (hδ : 0 < δ) :
    (∫ t, |samplingSmooth H (Set.Icc a b) t -
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) t| ∂ν) ≤
      12*δ + 1/(4*(H : ℝ)*δ^2) := by
  let E := Set.Icc a b
  let B := samplingBoundary a b δ
  let C := 1/(4*(H : ℝ)*δ^2)
  let f := fun t => |samplingSmooth H E t - E.indicator (fun _ => (1 : ℝ)) t|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBm : MeasurableSet B := samplingBoundary_measurable a b δ
  have hfm : Measurable f := by
    have hi : Measurable (E.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator measurableSet_Icc
    simpa only [Real.norm_eq_abs, Pi.sub_apply, f] using ((samplingSmooth_continuous H E).measurable.sub hi).norm
  have hfi : Integrable f ν := (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact samplingSmooth_indicator_error_le_one H hH E t))
  have hle (t : ℝ) : f t ≤ B.indicator (fun _ => (1 : ℝ)) t + C := by
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht]
      exact (samplingSmooth_indicator_error_le_one H hH E t).trans (by linarith)
    · rw [Set.indicator_of_notMem ht, zero_add]
      have hn := not_or.mp ht
      have hn' := not_or.mp hn.1
      have hmid : t ∈ Set.Icc δ (1-δ) := by simpa only [Set.mem_compl_iff, not_not] using hn'.1
      have ha : δ < |t-a| := by
        by_contra hh
        have hab := abs_le.mp (le_of_not_gt hh)
        exact hn'.2 ⟨by linarith [hab.1], by linarith [hab.2]⟩
      have hb : δ < |t-b| := by
        by_contra hh
        have hab := abs_le.mp (le_of_not_gt hh)
        exact hn.2 ⟨by linarith [hab.1], by linarith [hab.2]⟩
      exact samplingSmooth_interval_error H hH a b δ t hδ hmid.1 hmid.2 ha hb
  have hBμ : ν B ≤ ENNReal.ofReal (12*δ) := by
    calc
      _ ≤ ((2 : ℝ≥0∞) • unitIntervalMeasure) B := hν B
      _ = 2 * unitIntervalMeasure B := rfl
      _ ≤ 2 * ENNReal.ofReal (6*δ) := by gcongr; exact samplingBoundary_measure a b δ hδ.le
      _ = _ := by rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
  have hBreal : (ν B).toReal ≤ 12*δ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBμ
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hh := integral_mono_ae hfi (((integrable_const (1 : ℝ)).indicator hBm).add (integrable_const C))
    (Filter.Eventually.of_forall hle)
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_const (1 : ℝ)).indicator hBm) (integrable_const C), integral_indicator hBm] at hh
  simp [measureReal_def] at hh
  change (∫ t, f t ∂ν) ≤ 12*δ+C
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_Rectangle
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

theorem integrable_unit_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs,abs_of_nonneg (hbound x).1] using (hbound x).2)

theorem product_difference_unit_bound (a b c d : ℝ)
    (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    _ ≤ |a-c|+|b-d| := by nlinarith [abs_nonneg (a-c),abs_nonneg (b-d)]

/-- Uniform marginal smoothing errors control a product test under a
possibly dependent joint law. -/
theorem integral_product_smoothing_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g a b : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (ha : Measurable a) (hb : Measurable b)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hab : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (hbb : ∀ x, 0 ≤ b x ∧ b x ≤ 1) :
    |(∫ x, f x*g x ∂μ)-(∫ x, a x*b x ∂μ)| ≤
      (∫ x, |f x-a x| ∂μ)+(∫ x, |g x-b x| ∂μ) := by
  have hfg : Integrable (fun x => f x*g x) μ := integrable_unit_bounded μ _ (hf.mul hg)
    (fun x => ⟨mul_nonneg (hfb x).1 (hgb x).1, by nlinarith [(hfb x).1,(hfb x).2,(hgb x).1,(hgb x).2]⟩)
  have habi : Integrable (fun x => a x*b x) μ := integrable_unit_bounded μ _ (ha.mul hb)
    (fun x => ⟨mul_nonneg (hab x).1 (hbb x).1, by nlinarith [(hab x).1,(hab x).2,(hbb x).1,(hbb x).2]⟩)
  have hfa := (integrable_unit_bounded μ f hf hfb).sub (integrable_unit_bounded μ a ha hab)
  have hgb' := (integrable_unit_bounded μ g hg hgb).sub (integrable_unit_bounded μ b hb hbb)
  have hfa' : Integrable (fun x => |f x-a x|) μ := by simpa [Real.norm_eq_abs] using hfa.norm
  have hgb'' : Integrable (fun x => |g x-b x|) μ := by simpa [Real.norm_eq_abs] using hgb'.norm
  rw [← integral_sub hfg habi]
  calc
    _ ≤ ∫ x, |f x*g x-a x*b x| ∂μ := by simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x*g x-a x*b x)
    _ ≤ ∫ x, |f x-a x|+|g x-b x| ∂μ := by
      apply integral_mono_ae
      · simpa [Real.norm_eq_abs] using (hfg.sub habi).norm
      · exact hfa'.add hgb''
      · exact Filter.Eventually.of_forall (fun x => product_difference_unit_bound _ _ _ _ (hgb x) (hab x))
    _ = _ := integral_add hfa' hgb''

/-- Explicit rectangle discrepancy derived from actual marginal domination
and joint Fourier estimates. No two-dimensional density is required. -/
theorem sampling_rectangle_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hdomX : μ.map X ≤ (2 : ℝ≥0∞) • unitIntervalMeasure)
    (hdomY : μ.map Y ≤ (2 : ℝ≥0∞) • unitIntervalMeasure)
    (H : ℕ) (hH : 0 < H) (a b a' b' δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hFourier : ∀ v w : ℤ, |v| < (H : ℤ) → |w| < (H : ℤ) → (v ≠ 0 ∨ w ≠ 0) →
      ‖∫ θ, samplingCharacter v (X θ)*samplingCharacter w (Y θ) ∂μ‖ ≤ ε) :
    |(μ {θ | X θ ∈ Set.Icc a b ∧ Y θ ∈ Set.Icc a' b'}).toReal -
      (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc a' b')).toReal| ≤
      24*δ+1/(2*(H : ℝ)*δ^2)+(H : ℝ)^2*ε := by
  let E := Set.Icc a b
  let E' := Set.Icc a' b'
  let f := fun θ => E.indicator (fun _ => (1 : ℝ)) (X θ)
  let g := fun θ => E'.indicator (fun _ => (1 : ℝ)) (Y θ)
  let A := fun θ => samplingSmooth H E (X θ)
  let B := fun θ => samplingSmooth H E' (Y θ)
  have hf : Measurable f := (measurable_const.indicator measurableSet_Icc).comp hX
  have hg : Measurable g := (measurable_const.indicator measurableSet_Icc).comp hY
  have hA : Measurable A := (samplingSmooth_continuous H E).measurable.comp hX
  have hB : Measurable B := (samplingSmooth_continuous H E').measurable.comp hY
  have hfb (θ) : 0 ≤ f θ ∧ f θ ≤ 1 := by
    dsimp [f]; by_cases he : X θ ∈ E <;> simp [he]
  have hgb (θ) : 0 ≤ g θ ∧ g θ ≤ 1 := by
    dsimp [g]; by_cases he : Y θ ∈ E' <;> simp [he]
  have hprod := integral_product_smoothing_error μ f g A B hf hg hA hB hfb hgb
    (fun θ => samplingSmooth_bounds H hH E (X θ)) (fun θ => samplingSmooth_bounds H hH E' (Y θ))
  have : IsProbabilityMeasure (μ.map X) := ⟨by rw [Measure.map_apply hX MeasurableSet.univ]; simp⟩
  have : IsProbabilityMeasure (μ.map Y) := ⟨by rw [Measure.map_apply hY MeasurableSet.univ]; simp⟩
  have hex := samplingSmooth_expected_error (μ.map X) hdomX H hH a b δ hδ
  have hey := samplingSmooth_expected_error (μ.map Y) hdomY H hH a' b' δ hδ
  have hem (a b : ℝ) : Measurable (fun t => |samplingSmooth H (Set.Icc a b) t-
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) t|) := by
    have hi : Measurable ((Set.Icc a b).indicator (fun _ => (1 : ℝ))) := measurable_const.indicator measurableSet_Icc
    simpa [Real.norm_eq_abs] using ((samplingSmooth_continuous H (Set.Icc a b)).measurable.sub hi).norm
  rw [integral_map hX.aemeasurable (hem a b).aestronglyMeasurable] at hex
  rw [integral_map hY.aemeasurable (hem a' b').aestronglyMeasurable] at hey
  have hfint : (∫ θ, f θ*g θ ∂μ) = (μ {θ | X θ ∈ E ∧ Y θ ∈ E'}).toReal := by
    have he : (fun θ => f θ*g θ) = {θ | X θ ∈ E ∧ Y θ ∈ E'}.indicator (fun _ => (1 : ℝ)) := by
      funext θ
      dsimp [f,g]
      by_cases hx : X θ ∈ E <;> by_cases hy : Y θ ∈ E' <;> simp [hx,hy]
    rw [he,integral_indicator (by exact (hX measurableSet_Icc).inter (hY measurableSet_Icc))]
    simp [measureReal_def]
  have hsm := samplingSmooth_pair_error μ X Y hX hY H hH E E' ε hε hFourier
  simp_rw [← Complex.ofReal_mul] at hsm
  rw [integral_complex_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hsm
  change |(∫ θ, A θ*B θ ∂μ)-(unitIntervalMeasure E).toReal*(unitIntervalMeasure E').toReal| ≤ _ at hsm
  have hex' : (∫ θ, |f θ-A θ| ∂μ) ≤ 12*δ+1/(4*(H : ℝ)*δ^2) := by
    simpa only [f,A,abs_sub_comm] using hex
  have hey' : (∫ θ, |g θ-B θ| ∂μ) ≤ 12*δ+1/(4*(H : ℝ)*δ^2) := by
    simpa only [g,B,abs_sub_comm] using hey
  rw [← hfint]
  have htri := abs_sub_le (∫ θ, f θ*g θ ∂μ) (∫ θ, A θ*B θ ∂μ)
    ((unitIntervalMeasure E).toReal*(unitIntervalMeasure E').toReal)
  have hc : 2*(1/(4*(H : ℝ)*δ^2)) = 1/(2*(H : ℝ)*δ^2) := by ring
  nlinarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_OrbitSampling_Discrepancy
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

theorem samplingCharacter_pair_expression (v w : ℤ) (a b : ℝ) :
    samplingCharacter v a*samplingCharacter w b =
      Complex.exp (2*Real.pi*Complex.I*((v : ℂ)*(a : ℂ)+(w : ℂ)*(b : ℂ))) := by
  unfold samplingCharacter
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Rectangle discrepancy for the actual pair law of the deterministic
selected powers, with every probabilistic hypothesis discharged. -/
theorem sourceSampling_rectangle_bound (s : ℕ) (hs : 200000 ≤ sourceBlockSize s)
    (i : SourceCoordinate) (hi : i.1 ≤ s) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers s) (hn' : n' ∈ sourceSamplingPowers s) (hne : n ≠ n')
    (a b a' b' : ℝ) :
    |(sourceAngleLaw {θ | Int.fract ((n : ℝ)*θ i) ∈ Set.Icc a b ∧
        Int.fract ((n' : ℝ)*θ i) ∈ Set.Icc a' b'}).toReal -
      (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc a' b')).toReal| ≤
      26*(sourceBlockSize s : ℝ)^(-80 : ℝ) := by
  let m := sourceBlockSize s
  have hm0 : (0 : ℝ) < m := sourceBlockSize_pos s
  have hm1 : (1 : ℝ) ≤ m := by
    have hm : (200000 : ℝ) ≤ m := by exact_mod_cast hs
    linarith
  let δ : ℝ := (m : ℝ)^(-80 : ℝ)
  let ε : ℝ := Real.pi⁻¹*(m : ℝ)^(-1000 : ℝ)
  have hH : 0 < samplingH m := pow_pos (by exact_mod_cast hm0) 300
  have hphase (n : ℤ) : Measurable (fun θ : SourceCoordinate → ℝ => Int.fract ((n : ℝ)*θ i)) :=
    sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i))
  have hh := sampling_rectangle_discrepancy sourceAngleLaw _ _ (hphase n) (hphase n')
    (sourceSampling_phase_domination s hs i hi n hn) (sourceSampling_phase_domination s hs i hi n' hn')
    (samplingH m) hH a b a' b' δ ε (by dsimp [δ]; positivity) (by dsimp [ε]; positivity)
    (fun v w hv hw hne' => by
      simp_rw [samplingCharacter_pair_expression]
      exact sourceSampling_pair_fourier_bound s hs i hi n n' hn hn' hne v w hv.le hw.le hne')
  apply hh.trans
  have htail : 1/(2*(samplingH m : ℝ)*δ^2) = (1/2 : ℝ)*(m : ℝ)^(-140 : ℝ) := by
    dsimp [samplingH,δ]
    norm_num [Real.rpow_neg,Real.rpow_ofNat,hm0.le]
    field_simp
  have hfour : (samplingH m : ℝ)^2*ε = Real.pi⁻¹*(m : ℝ)^(-400 : ℝ) := by
    dsimp [samplingH,ε]
    norm_num [Real.rpow_neg,Real.rpow_ofNat,hm0.le]
    field_simp
  rw [htail,hfour]
  have h140 : (m : ℝ)^(-140 : ℝ) ≤ δ := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have h400 : (m : ℝ)^(-400 : ℝ) ≤ δ := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hpi : Real.pi⁻¹ ≤ 1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (show 1 ≤ Real.pi by linarith [Real.two_le_pi])
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hp0 : 0 ≤ (m : ℝ)^(-400 : ℝ) := by positivity
  change 24*δ+1/2*(m : ℝ)^(-140 : ℝ)+Real.pi⁻¹*(m : ℝ)^(-400 : ℝ) ≤ 26*δ
  nlinarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_Weights
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

/-- In the second diagonal orientation the nonzero weight has no wrap and
the original coordinate is exactly s-t, as in the source calculation. -/
theorem samplingWeight_second_no_wrap (h α s t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hw : samplingWeight false h α (Int.fract (s-t)) t ≠ 0) :
    t < s ∧ Int.fract (s-t) = s-t := by
  have hsp := samplingWeight_support false h α (Int.fract (s-t)) t hh hh1 hα
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩ hw
  have hcut : α ≤ samplingDistance (Int.fract (s-t)) := by
    unfold samplingWeight at hw
    simp only [Bool.false_eq_true,ite_false] at hw
    split_ifs at hw with hc
    · exact hc.1
    · exact False.elim (hw rfl)
  have hts : t < s := by
    by_contra hn
    have hle : s ≤ t := le_of_not_gt hn
    by_cases he : s = t
    · subst t
      simp [samplingDistance] at hcut
      linarith
    · have hst : s-t < 0 := sub_neg.mpr (lt_of_le_of_ne hle he)
      have hf : ⌊s-t⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr
        ⟨by norm_num; linarith [hs.1,ht.2],by norm_num; linarith⟩
      rw [Int.fract,hf] at hsp
      norm_num at hsp
      linarith [hsp.2,hs.1]
  exact ⟨hts,Int.fract_eq_self.mpr ⟨by linarith,by linarith [hs.2,ht.1]⟩⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_FirstDiscrepancy
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- The actual selected phase laws are atomless, despite possible dependence
between two phases. Only their already proved marginal domination is used. -/
theorem sourceSampling_phase_null_singletons (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    NullSingletonClass (sourceAngleLaw.map (fun θ => Int.fract ((n : ℝ)*θ i))) := by
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  constructor
  intro x
  have hdom := sourceSampling_phase_domination stage hs i hi n hn
  exact le_antisymm ((hdom {x}).trans_eq (by simp)) bot_le

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_LayerCake
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

/-- Finite layer-cake formula for a product, valid even for a singular joint law. -/
theorem sampling_product_layerCake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (C : ℝ) (_hC : 0 ≤ C)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    (∫ x, f x*g x ∂μ) =
      ∫ r in Set.Ioc 0 C, ∫ t in Set.Ioc 0 C,
        (μ {x | r ≤ f x ∧ t ≤ g x}).toReal := by
  let ν := volume.restrict (Set.Ioc 0 C)
  let K : (ℝ × ℝ) × Ω → ℝ := fun p =>
    if p.1.1 ≤ f p.2 ∧ p.1.2 ≤ g p.2 then 1 else 0
  have hK : Measurable K := measurable_const.ite
    ((measurableSet_le measurable_fst.fst (hf.comp measurable_snd)).inter
      (measurableSet_le measurable_fst.snd (hg.comp measurable_snd))) measurable_const
  have hKb (p) : |K p| ≤ 1 := by dsimp [K]; split_ifs <;> norm_num
  have hKi := sampling_integrable_bounded ((ν.prod ν).prod μ) K hK 1 hKb
  have hpoint (x : Ω) : (∫ p, K (p,x) ∂ν.prod ν) = f x*g x := by
    have hik : Integrable (fun p => K (p,x)) (ν.prod ν) :=
      sampling_integrable_bounded (ν.prod ν) _
        (hK.comp (measurable_id.prodMk measurable_const)) 1 (fun p => hKb (p,x))
    rw [integral_prod _ hik]
    have he (r t : ℝ) : K ((r,t),x) =
        (Set.Iic (f x)).indicator (fun _ => (1 : ℝ)) r *
        (Set.Iic (g x)).indicator (fun _ => (1 : ℝ)) t := by
      simp only [K,Set.indicator,Set.mem_Iic]; split_ifs <;> simp_all
    simp_rw [he,integral_const_mul,integral_mul_const]
    have hv (a : ℝ) (ha : 0 ≤ a ∧ a ≤ C) :
        (∫ r, (Set.Iic a).indicator (fun _ => (1 : ℝ)) r ∂ν) = a := by
      rw [integral_indicator measurableSet_Iic]
      simp only [integral_const,smul_eq_mul,mul_one,measureReal_def]
      dsimp [ν]
      rw [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
        Measure.restrict_apply measurableSet_Iic]
      have he : Set.Iic a ∩ Set.Ioc 0 C = Set.Ioc 0 a := by
        ext r; simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Ioc]
        constructor
        · intro h; exact ⟨h.2.1,h.1⟩
        · intro h; exact ⟨h.2,h.1,h.2.trans ha.2⟩
      rw [he,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal ha.1]
    rw [hv _ (hfb x),hv _ (hgb x)]
  calc
    _ = ∫ x, ∫ p, K (p,x) ∂ν.prod ν ∂μ := by simp_rw [hpoint]
    _ = ∫ p, ∫ x, K (p,x) ∂μ ∂ν.prod ν := (integral_integral_swap hKi).symm
    _ = ∫ r, ∫ t, ∫ x, K ((r,t),x) ∂μ ∂ν ∂ν :=
      integral_prod _ hKi.integral_prod_left
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with r
      apply integral_congr_ae
      filter_upwards [] with t
      have he : (fun x => K ((r,t),x)) =
          {x | r ≤ f x ∧ t ≤ g x}.indicator (fun _ => (1 : ℝ)) := by funext x; simp [K,Set.indicator]
      have hm : MeasurableSet {x | r ≤ f x ∧ t ≤ g x} :=
        (measurableSet_le measurable_const hf).inter (measurableSet_le measurable_const hg)
      rw [he,integral_indicator hm]
      simp [measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_LayerDiscrepancy
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

theorem sampling_measureReal_le_one {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (S : Set α) : |(ρ S).toReal| ≤ 1 := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (ρ Set.univ).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ S))
    _ = 1 := by simp

/-- Joint superlevel probabilities are measurable in both thresholds. -/
theorem sampling_levelMass_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : ℝ × ℝ => (μ {x | p.1 ≤ f x ∧ p.2 ≤ g x}).toReal) := by
  let K : (ℝ × ℝ) × Ω → ℝ := fun p =>
    if p.1.1 ≤ f p.2 ∧ p.1.2 ≤ g p.2 then 1 else 0
  have hK : Measurable K := measurable_const.ite
    ((measurableSet_le measurable_fst.fst (hf.comp measurable_snd)).inter
      (measurableSet_le measurable_fst.snd (hg.comp measurable_snd))) measurable_const
  have he (p : ℝ × ℝ) : (∫ x, K (p,x) ∂μ) =
      (μ {x | p.1 ≤ f x ∧ p.2 ≤ g x}).toReal := by
    have hs : MeasurableSet {x | p.1 ≤ f x ∧ p.2 ≤ g x} :=
      (measurableSet_le measurable_const hf).inter (measurableSet_le measurable_const hg)
    have hk : (fun x => K (p,x)) =
        {x | p.1 ≤ f x ∧ p.2 ≤ g x}.indicator (fun _ => (1 : ℝ)) := by
      funext x; simp [K,Set.indicator]
    rw [hk,integral_indicator hs]
    simp [measureReal_def]
  have hKm : StronglyMeasurable (Function.uncurry (fun p x => K (p,x))) := hK.stronglyMeasurable
  simpa only [he] using (hKm.integral_prod_right (ν := μ)).measurable

/-- Uniform superlevel discrepancy controls weighted pair integrals. The
threshold square has area C^2; no density for the joint law is needed. -/
theorem sampling_layer_discrepancy {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : Ω → ℝ) (f₀ g₀ : Ψ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf₀ : Measurable f₀) (hg₀ : Measurable g₀)
    (C δ : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ C) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ C)
    (hf₀b : ∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ C) (hg₀b : ∀ x, 0 ≤ g₀ x ∧ g₀ x ≤ C)
    (hlevel : ∀ r t : ℝ, 0 < r → r ≤ C → 0 < t → t ≤ C →
      |(μ {x | r ≤ f x ∧ t ≤ g x}).toReal -
        (ν {x | r ≤ f₀ x ∧ t ≤ g₀ x}).toReal| ≤ δ) :
    |(∫ x, f x*g x ∂μ)-(∫ x, f₀ x*g₀ x ∂ν)| ≤ δ*C^2 := by
  let τ := volume.restrict (Set.Ioc 0 C)
  let F : ℝ × ℝ → ℝ := fun p => (μ {x | p.1 ≤ f x ∧ p.2 ≤ g x}).toReal
  let G : ℝ × ℝ → ℝ := fun p => (ν {x | p.1 ≤ f₀ x ∧ p.2 ≤ g₀ x}).toReal
  have hFm : Measurable F := sampling_levelMass_measurable μ f g hf hg
  have hGm : Measurable G := sampling_levelMass_measurable ν f₀ g₀ hf₀ hg₀
  have hFi := sampling_integrable_bounded (τ.prod τ) F hFm 1 (fun p => by dsimp [F]; exact sampling_measureReal_le_one μ _)
  have hGi := sampling_integrable_bounded (τ.prod τ) G hGm 1 (fun p => by dsimp [G]; exact sampling_measureReal_le_one ν _)
  rw [sampling_product_layerCake μ f g hf hg C hC hfb hgb,
    sampling_product_layerCake ν f₀ g₀ hf₀ hg₀ C hC hf₀b hg₀b]
  change |(∫ r, ∫ t, F (r,t) ∂τ ∂τ)-(∫ r, ∫ t, G (r,t) ∂τ ∂τ)| ≤ _
  rw [← integral_prod F hFi,← integral_prod G hGi,← integral_sub hFi hGi]
  have hb : ∀ᵐ p ∂τ.prod τ, ‖F p-G p‖ ≤ δ := by
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {p : ℝ × ℝ | ‖F p-G p‖ ≤ δ} from
      measurableSet_le (hFm.sub hGm).norm measurable_const)).mpr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    simpa [Real.norm_eq_abs,F,G] using hlevel r t hr.1 hr.2 ht.1 ht.2
  have hi := norm_integral_le_of_norm_le_const hb
  have hm : (τ.prod τ).real Set.univ = C^2 := by
    rw [measureReal_def,← Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
    simp [τ,Real.volume_Ioc,ENNReal.toReal_ofReal hC,pow_two]
  simpa only [Real.norm_eq_abs,hm,mul_comm] using hi

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_IntervalSums
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

theorem samplingClosedIndicator_measurable (a b : ℝ) :
    Measurable (samplingClosedIndicator a b) := measurable_const.indicator measurableSet_Icc

theorem samplingClosedIndicator_bounds (a b t : ℝ) :
    0 ≤ samplingClosedIndicator a b t ∧ samplingClosedIndicator a b t ≤ 1 := by
  simp only [samplingClosedIndicator,Set.indicator]; split_ifs <;> norm_num

theorem samplingClosedIndicator_integral (a b : ℝ) :
    (∫ t, samplingClosedIndicator a b t ∂unitIntervalMeasure) =
      (unitIntervalMeasure (Set.Icc a b)).toReal := by
  unfold samplingClosedIndicator
  rw [integral_indicator measurableSet_Icc]
  simp [measureReal_def]

theorem samplingClosedIndicator_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (a b c d : ℝ) :
    (∫ x, samplingClosedIndicator a b (X x)*samplingClosedIndicator c d (Y x) ∂μ) =
      (μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal := by
  have hs : MeasurableSet {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d} :=
    (measurableSet_Icc.preimage hX).inter (measurableSet_Icc.preimage hY)
  have he : (fun x => samplingClosedIndicator a b (X x)*samplingClosedIndicator c d (Y x)) =
      {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}.indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [samplingClosedIndicator,Set.indicator,Set.mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he,integral_indicator hs]
  simp [measureReal_def]

/-- Two intervals in each variable cost four rectangle discrepancies. -/
theorem sampling_two_intervals_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (δ : ℝ)
    (hrect : ∀ a b c d : ℝ,
      |(μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal -
        (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc c d)).toReal| ≤ δ)
    (a b c d : Fin 2 → ℝ) :
    |(∫ x, (∑ j, samplingClosedIndicator (a j) (b j) (X x))*
        (∑ k, samplingClosedIndicator (c k) (d k) (Y x)) ∂μ) -
      (∫ t, ∑ j, samplingClosedIndicator (a j) (b j) t ∂unitIntervalMeasure)*
      (∫ t, ∑ k, samplingClosedIndicator (c k) (d k) t ∂unitIntervalMeasure)| ≤ 4*δ := by
  let f (j : Fin 2) := samplingClosedIndicator (a j) (b j)
  let g (k : Fin 2) := samplingClosedIndicator (c k) (d k)
  have hi (j k : Fin 2) : Integrable (fun x => f j (X x)*g k (Y x)) μ := by
    apply sampling_integrable_bounded μ _
      (((samplingClosedIndicator_measurable _ _).comp hX).mul
        ((samplingClosedIndicator_measurable _ _).comp hY)) 1
    intro x
    have h1 := samplingClosedIndicator_bounds (a j) (b j) (X x)
    have h2 := samplingClosedIndicator_bounds (c k) (d k) (Y x)
    simp only [Pi.mul_apply,Function.comp_apply]
    rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]
    nlinarith
  have hif (j : Fin 2) : Integrable (f j) unitIntervalMeasure :=
    integrable_unit_bounded _ _ (samplingClosedIndicator_measurable _ _) (samplingClosedIndicator_bounds _ _)
  have hig (k : Fin 2) : Integrable (g k) unitIntervalMeasure :=
    integrable_unit_bounded _ _ (samplingClosedIndicator_measurable _ _) (samplingClosedIndicator_bounds _ _)
  change |(∫ x, (∑ j, f j (X x))*(∑ k, g k (Y x)) ∂μ) -
    (∫ t, ∑ j, f j t ∂unitIntervalMeasure)*(∫ t, ∑ k, g k t ∂unitIntervalMeasure)| ≤ _
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k)]
  rw [integral_finsetSum _ (fun j _ => hif j),integral_finsetSum _ (fun k _ => hig k)]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin 2, ∑ k : Fin 2,
        |(∫ x, f j (X x)*g k (Y x) ∂μ)-
          (∫ t, f j t ∂unitIntervalMeasure)*(∫ t, g k t ∂unitIntervalMeasure)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _j : Fin 2, ∑ _k : Fin 2, δ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      simpa only [f,g,samplingClosedIndicator_pair μ X Y hX hY,
        samplingClosedIndicator_integral] using hrect (a j) (b j) (c k) (d k)
    _ = _ := by simp; ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SecondDensity
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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_TestedSecondMoment
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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SecondInterval
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

theorem samplingSecondWeight_support_iff (h α s t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingSecondWeight h α s t ≠ 0 ↔
      0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α := by
  have hplus : 0 < 1+h := by linarith
  have hminus : 0 < 1-h := by linarith
  constructor
  · intro hw
    have hf := (samplingWeight_second_no_wrap h α s t hh hh1 hα hs ht hw).2
    have hc : α ≤ samplingDistance (s-t) ∧ 0 < t ∧ t < h*samplingDistance (s-t) := by
      unfold samplingSecondWeight samplingWeight at hw
      simp only [Bool.false_eq_true,ite_false,hf] at hw
      split_ifs at hw with hc
      · exact hc
      · exact False.elim (hw rfl)
    have hcut := le_min_iff.mp hc.1
    have hleft : t < h*(s-t) := hc.2.2.trans_le
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hh.le)
    have hright : t < h*(1-(s-t)) := hc.2.2.trans_le
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hh.le)
    refine ⟨hc.2.1,?_,hcut.1,by linarith [hcut.2]⟩
    unfold samplingSecondLength
    rw [lt_min_iff,lt_div_iff₀ hplus,lt_div_iff₀ hminus]
    constructor <;> nlinarith
  · rintro ⟨ht0,htL,hcut,hcut'⟩
    have hz : s-t ∈ Set.Ico (0 : ℝ) 1 := ⟨hα.le.trans hcut,by linarith⟩
    have hf := Int.fract_eq_self.mpr hz
    have hL := lt_min_iff.mp htL
    have hl := (lt_div_iff₀ hplus).mp hL.1
    have hr := (lt_div_iff₀ hminus).mp hL.2
    have htl : t < h*(s-t) := by nlinarith
    have htr : t < h*(1-(s-t)) := by nlinarith
    have hd : α ≤ samplingDistance (s-t) := le_min hcut (by linarith)
    have htd : t < h*samplingDistance (s-t) := by
      unfold samplingDistance
      rw [mul_min_of_nonneg _ _ hh.le]
      exact lt_min htl htr
    have hp : 0 < h*samplingDistance (s-t) := mul_pos hh (hα.trans_le hd)
    simp [samplingSecondWeight,samplingWeight,hf,hd,ht0,htd,(hα.trans_le hd).ne',hh.ne']

/-- Exact reciprocal on the actual second-oriented support. -/
theorem samplingSecondWeight_interval (h α s t : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingSecondWeight h α s t =
      if 0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α
      then 1/(h*samplingDistance (s-t)) else 0 := by
  by_cases hw : samplingSecondWeight h α s t ≠ 0
  · have hc := (samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mp hw
    have hf := (samplingWeight_second_no_wrap h α s t hh hh1 hα hs ht hw).2
    rw [ite_eq_left hc]
    unfold samplingSecondWeight samplingWeight at *
    simp only [Bool.false_eq_true,ite_false,hf] at *
    split_ifs at * <;> simp_all
  · rw [not_ne_iff] at hw
    have hc : ¬ (0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α) := by
      intro hc
      exact ((samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mpr hc) hw
    rw [ite_eq_right hc,hw]

/-- The x-test intersects that support with a reflected interval, while the
y-test is constant in the phase variable. -/
theorem samplingTestedSecondWeight_interval (h α : ℝ) (G : Set ℝ) (a c s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedSecondWeight h α (Set.Icc a c) G s t =
      (Set.Ioo 0 (samplingSecondLength h s) ∩
        Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a))).indicator
        (fun t => if s ∈ G then 1/(h*samplingDistance (s-t)) else 0) t := by
  have heq : t ∈ Set.Ioo 0 (samplingSecondLength h s) ∩
      Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a)) ↔
      (0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α) ∧ s-t ∈ Set.Icc a c := by
    simp only [Set.mem_inter_iff,Set.mem_Ioo,Set.mem_Icc,max_le_iff,le_min_iff]
    constructor
    · rintro ⟨ht0,hL⟩
      exact ⟨⟨ht0.1,ht0.2,by linarith [hL.2.1],by linarith [hL.1.1]⟩,
        ⟨by linarith [hL.2.2],by linarith [hL.1.2]⟩⟩
    · rintro ⟨⟨ht0,hL,hcut,hcut'⟩,ha,hc⟩
      exact ⟨⟨ht0,hL⟩,⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩⟩
  by_cases hw : samplingSecondWeight h α s t ≠ 0
  · have hc := (samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mp hw
    have hf := (samplingWeight_second_no_wrap h α s t hh hh1 hα hs ht hw).2
    rw [samplingTestedSecondWeight,samplingSecondWeight_interval h α s t hh hh1 hα hs ht,
      ite_eq_left hc,hf]
    simp only [Set.indicator,heq,hc,true_and]
    split_ifs <;> simp_all
  · have hc : ¬ (0 < t ∧ t < samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α) := by
      intro hc
      exact hw ((samplingSecondWeight_support_iff h α s t hh hh1 hα hs ht).mpr hc)
    have hz := not_ne_iff.mp hw
    simp only [samplingTestedSecondWeight,hz,ite_self,Set.indicator,heq,hc,false_and,ite_false]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SecondLevels
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

/-- A reciprocal superlevel is the union of two endpoint intervals. -/
theorem sampling_reciprocal_level (h r z : ℝ) (hh : 0 < h) (hr : 0 < r)
    (hz : 0 < z) (hz1 : z < 1) :
    r ≤ 1/(h*samplingDistance z) ↔
      (z ≤ 1/2 ∧ z ≤ 1/(h*r)) ∨ (1/2 ≤ z ∧ 1-z ≤ 1/(h*r)) := by
  have hd : 0 < samplingDistance z := lt_min hz (by linarith)
  have hd' : 0 < h*samplingDistance z := mul_pos hh hd
  have hhr : 0 < h*r := mul_pos hh hr
  rw [le_div_iff₀ hd']
  by_cases hc : z ≤ 1/2
  · have he : samplingDistance z = z := min_eq_left (by linarith)
    rw [he]
    constructor
    · intro ha
      exact Or.inl ⟨hc,(le_div_iff₀ hhr).mpr (by nlinarith)⟩
    · rintro (ha|ha)
      · have hb := (le_div_iff₀ hhr).mp ha.2; nlinarith
      · have hb := (le_div_iff₀ hhr).mp ha.2
        have heq : z = 1/2 := le_antisymm hc ha.1
        rw [heq] at *
        nlinarith
  · have he : samplingDistance z = 1-z := min_eq_right (by linarith)
    rw [he]
    constructor
    · intro ha
      exact Or.inr ⟨by linarith,(le_div_iff₀ hhr).mpr (by nlinarith)⟩
    · rintro (ha|ha)
      · exact (hc ha.1).elim
      · have hb := (le_div_iff₀ hhr).mp ha.2; nlinarith

/-- Away from three possible jumps, the exact level indicator is the sum of
two closed-interval indicators. No variation theorem is assumed. -/
theorem samplingTestedSecond_level_intervals (h α : ℝ) (G : Set ℝ) (a c s r t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (hr : 0 < r) (hsG : s ∈ G)
    (ht0 : t ≠ 0) (htL : t ≠ samplingSecondLength h s) (htmid : t ≠ s-1/2) :
    (if r ≤ samplingTestedSecondWeight h α (Set.Icc a c) G s t then (1 : ℝ) else 0) =
      (samplingSecondLevelLeft h α a c s r).indicator (fun _ => (1 : ℝ)) t +
      (samplingSecondLevelRight h α a c s r).indicator (fun _ => (1 : ℝ)) t := by
  rw [samplingTestedSecondWeight_interval h α G a c s t hh hh1 hα hs ht]
  have hsupport : t ∈ Set.Ioo 0 (samplingSecondLength h s) ∩
      Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a)) ↔
      0 ≤ t ∧ t ≤ samplingSecondLength h s ∧ α ≤ s-t ∧ s-t ≤ 1-α ∧
        a ≤ s-t ∧ s-t ≤ c := by
    simp only [Set.mem_inter_iff,Set.mem_Ioo,Set.mem_Icc,max_le_iff,le_min_iff]
    constructor
    · rintro ⟨h1,h2⟩; rcases h1 with ⟨h1,h1'⟩; rcases h2 with ⟨⟨h2,h3⟩,h4,h5⟩
      exact ⟨h1.le,h1'.le,by linarith,by linarith,by linarith,by linarith⟩
    · rintro ⟨h1,h2,h3,h4,h5,h6⟩
      exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm ht0),lt_of_le_of_ne h2 htL⟩,
        ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩⟩
  by_cases hc : t ∈ Set.Ioo 0 (samplingSecondLength h s) ∩
      Set.Icc (max (s-(1-α)) (s-c)) (min (s-α) (s-a))
  · have hz := hsupport.mp hc
    rw [Set.indicator_of_mem hc,ite_eq_left hsG]
    simp only [sampling_reciprocal_level h r (s-t) hh hr (hα.trans_le hz.2.2.1) (by linarith [hz.2.2.2.1])]
    simp only [samplingSecondLevelLeft,samplingSecondLevelRight,Set.indicator,
      Set.mem_Icc,max_le_iff,le_min_iff]
    have hm : s-t ≠ (1/2 : ℝ) := by intro he; apply htmid; linarith
    split_ifs <;> simp_all <;> grind
  · have hn := (not_congr hsupport).mp hc
    rw [Set.indicator_of_notMem hc,ite_eq_right (by linarith : ¬ r ≤ (0 : ℝ))]
    simp only [samplingSecondLevelLeft,samplingSecondLevelRight,Set.indicator,
      Set.mem_Icc,max_le_iff,le_min_iff]
    split_ifs <;> simp_all <;> grind

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SecondLevelAE
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

/-- The interval endpoints depend only on the weight and level, and work
simultaneously for every atomless law carried by [0,1). -/
theorem samplingTestedSecond_level_exists (h α : ℝ) (G : Set ℝ) (a c s r : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hr : 0 < r) :
    ∃ A B : Fin 2 → ℝ, ∀ (ν : Measure ℝ) [NullSingletonClass ν],
      (∀ᵐ t ∂ν, t ∈ Set.Ico (0 : ℝ) 1) →
      (fun t => if r ≤ samplingTestedSecondWeight h α (Set.Icc a c) G s t then (1 : ℝ) else 0) =ᵐ[ν]
        (fun t => ∑ j, samplingClosedIndicator (A j) (B j) t) := by
  by_cases hG : s ∈ G
  · refine ⟨![max 0 (max (s-(1-α)) (s-c)),
        max (max (max 0 (max (s-(1-α)) (s-c))) (s-1/2)) (s-1/(h*r))],
      ![min (min (min (samplingSecondLength h s) (min (s-α) (s-a))) (s-1/2)) (s-1+1/(h*r)),
        min (samplingSecondLength h s) (min (s-α) (s-a))],?_⟩
    intro ν _ hν
    filter_upwards [hν,
      ae_iff.mpr (show ν {t | ¬t ≠ 0} = 0 by simp),
      ae_iff.mpr (show ν {t | ¬t ≠ samplingSecondLength h s} = 0 by simp),
      ae_iff.mpr (show ν {t | ¬t ≠ s-1/2} = 0 by simp)] with t ht ht0 htL htm
    simpa [Fin.sum_univ_two,samplingClosedIndicator,samplingSecondLevelLeft,samplingSecondLevelRight]
      using samplingTestedSecond_level_intervals h α G a c s r t hh hh1 hα hs ht hr hG ht0 htL htm
  · refine ⟨fun _ => 1,fun _ => 0,?_⟩
    intro ν _ _
    apply Eventually.of_forall
    intro t
    simp [samplingTestedSecondWeight,hG,not_le.mpr hr,samplingClosedIndicator]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_Sampling_SecondDiscrepancy
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

theorem sampling_level_pair_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (r t : ℝ) :
    (∫ x, (if r ≤ f x then (1 : ℝ) else 0)*(if t ≤ g x then (1 : ℝ) else 0) ∂μ) =
      (μ {x | r ≤ f x ∧ t ≤ g x}).toReal := by
  have hs : MeasurableSet {x | r ≤ f x ∧ t ≤ g x} :=
    (measurableSet_le measurable_const hf).inter (measurableSet_le measurable_const hg)
  have he : (fun x => (if r ≤ f x then (1 : ℝ) else 0)*(if t ≤ g x then (1 : ℝ) else 0)) =
      {x | r ≤ f x ∧ t ≤ g x}.indicator (fun _ => (1 : ℝ)) := by
    funext x; simp only [Set.indicator,Set.mem_ofPred_eq]; split_ifs <;> simp_all
  rw [he,integral_indicator hs]
  simp [measureReal_def]

/-- The actual second-oriented reciprocal inherits rectangle discrepancy,
including both monotone pieces, cutoff jumps and reflected interval tests. -/
theorem samplingTestedSecond_pair_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    [NullSingletonClass (μ.map X)] [NullSingletonClass (μ.map Y)]
    (hXs : ∀ᵐ x ∂μ.map X, x ∈ Set.Ico (0 : ℝ) 1)
    (hYs : ∀ᵐ x ∂μ.map Y, x ∈ Set.Ico (0 : ℝ) 1)
    (δ : ℝ) (hrect : ∀ a b c d : ℝ,
      |(μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal -
        (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc c d)).toReal| ≤ δ)
    (h α : ℝ) (G : Set ℝ) (a c s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hG : MeasurableSet G)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ x, samplingTestedSecondWeight h α (Set.Icc a c) G s (X x)*
        samplingTestedSecondWeight h α (Set.Icc a c) G s (Y x) ∂μ)-
      samplingTestedSecondDensity h α (Set.Icc a c) G s^2| ≤
      (4*δ)*(max 1 (1/(h*α)))^2 := by
  let w := samplingTestedSecondWeight h α (Set.Icc a c) G s
  let C := max 1 (1/(h*α))
  have hw : Measurable w := (samplingTestedSecondWeight_measurable h α _ G measurableSet_Icc hG).comp
    (measurable_const.prodMk measurable_id)
  have hwb (t : ℝ) : 0 ≤ w t ∧ w t ≤ C :=
    ⟨(samplingTestedSecondWeight_bounds h α _ G s t hh hα).1,
      (samplingTestedSecondWeight_bounds h α _ G s t hh hα).2.trans
        (samplingWeight_bounds false h α _ t hh hα).2⟩
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  have hu : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Set.Ico (0 : ℝ) 1 :=
    self_mem_ae_restrict measurableSet_Ico
  have hl (r t : ℝ) (hr : 0 < r) (_hrC : r ≤ C) (ht : 0 < t) (_htC : t ≤ C) :
      |(μ {x | r ≤ w (X x) ∧ t ≤ w (Y x)}).toReal -
        (unitIntervalMeasure.prod unitIntervalMeasure {p : ℝ × ℝ | r ≤ w p.1 ∧ t ≤ w p.2}).toReal| ≤ 4*δ := by
    obtain ⟨A,B,hAB⟩ := samplingTestedSecond_level_exists h α G a c s r hh hh1 hα hs hr
    obtain ⟨D,E,hDE⟩ := samplingTestedSecond_level_exists h α G a c s t hh hh1 hα hs ht
    have hx := ae_of_ae_map hX.aemeasurable (hAB (μ.map X) hXs)
    have hy := ae_of_ae_map hY.aemeasurable (hDE (μ.map Y) hYs)
    have hpair : (∫ x, (if r ≤ w (X x) then (1 : ℝ) else 0)*
        (if t ≤ w (Y x) then (1 : ℝ) else 0) ∂μ) =
        ∫ x, (∑ j, samplingClosedIndicator (A j) (B j) (X x))*
          (∑ k, samplingClosedIndicator (D k) (E k) (Y x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hx,hy] with x hx hy
      rw [hx,hy]
    have hmeanr := integral_congr_ae (hAB unitIntervalMeasure hu)
    have hmeant := integral_congr_ae (hDE unitIntervalMeasure hu)
    rw [← sampling_level_pair_integral μ (fun x => w (X x)) (fun x => w (Y x)) (hw.comp hX) (hw.comp hY) r t,hpair,
      ← sampling_level_pair_integral (unitIntervalMeasure.prod unitIntervalMeasure) (fun p => w p.1) (fun p => w p.2)
        (hw.comp measurable_fst) (hw.comp measurable_snd) r t]
    rw [integral_prod_mul (fun x => if r ≤ w x then (1 : ℝ) else 0)
      (fun x => if t ≤ w x then (1 : ℝ) else 0)]
    change |_- (∫ x, if r ≤ w x then (1 : ℝ) else 0 ∂unitIntervalMeasure)*
      (∫ x, if t ≤ w x then (1 : ℝ) else 0 ∂unitIntervalMeasure)| ≤ _
    rw [hmeanr,hmeant]
    exact sampling_two_intervals_pair μ X Y hX hY δ hrect A B D E
  have hc := sampling_layer_discrepancy μ (unitIntervalMeasure.prod unitIntervalMeasure)
    (fun x => w (X x)) (fun x => w (Y x)) (fun p => w p.1) (fun p => w p.2)
    (hw.comp hX) (hw.comp hY) (hw.comp measurable_fst) (hw.comp measurable_snd)
    C (4*δ) (le_trans (by norm_num) (le_max_left _ _))
    (fun x => hwb (X x)) (fun x => hwb (Y x)) (fun p => hwb p.1) (fun p => hwb p.2) hl
  rw [integral_prod_mul w w] at hc
  simpa only [w,C,samplingTestedSecondDensity,pow_two] using hc

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ5_Hy.FiniteFactor_OrbitSampling_SecondCorrelation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- Uniform source height bound, for either marginal orientation. -/
theorem sourceSampling_max_height (stage : ℕ) :
    max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) ≤
      (sourceBlockSize stage : ℝ)^(3 : ℝ) := by
  have hm := sourceBlockSize_pos stage
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith
  apply max_le
  · exact Real.one_le_rpow hm1 (by norm_num)
  · have he : 1/(sourceSamplingWidth stage*sourceSamplingCutoff stage) =
        (sourceBlockSize stage : ℝ)^(13/5 : ℝ) := by
      unfold sourceSamplingWidth sourceSamplingCutoff
      rw [← Real.rpow_add hm]
      norm_num
      rw [Real.rpow_neg hm.le,inv_inv]
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)

/-- Actual second-diagonal pair error for the selected source powers.
All phase support, atomlessness and discrepancy hypotheses are discharged. -/
theorem sourceSampling_second_pair_error_oai (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (G : Set ℝ) (hG : MeasurableSet G) (a c s : ℝ) (hsx : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ θ, samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) G s (Int.fract ((n : ℝ)*θ i)) *
        samplingTestedSecondWeight (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (Set.Icc a c) G s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
      samplingTestedSecondDensity (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (Set.Icc a c) G s ^ 2| ≤
      104*(sourceBlockSize stage : ℝ)^(-74 : ℝ) := by
  have := sourceSampling_phase_null_singletons stage hs i hi n hn
  have := sourceSampling_phase_null_singletons stage hs i hi n' hn'
  have hm (k : ℤ) : Measurable (fun θ : SourceCoordinate → ℝ => Int.fract ((k : ℝ)*θ i)) :=
    sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i))
  have hsupport (k : ℤ) : ∀ᵐ t ∂sourceAngleLaw.map (fun θ => Int.fract ((k : ℝ)*θ i)),
      t ∈ Set.Ico (0 : ℝ) 1 := by
    apply (ae_map_iff (hm k).aemeasurable
      (show MeasurableSet {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1} from measurableSet_Ico)).mpr
    exact Eventually.of_forall (fun θ => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)
  have hp := sourceSampling_parameters stage
  have hb := samplingTestedSecond_pair_bound sourceAngleLaw
    (fun θ => Int.fract ((n : ℝ)*θ i)) (fun θ => Int.fract ((n' : ℝ)*θ i))
    (hm n) (hm n') (hsupport n) (hsupport n') _
    (sourceSampling_rectangle_bound stage hs i hi n n' hn hn' hne)
    _ _ G a c s hp.1 hp.2.1 hp.2.2 hG hsx
  let m : ℝ := sourceBlockSize stage
  let C := max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage))
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hC2 : C^2 ≤ m^(6 : ℝ) := by
    calc
      _ ≤ (m^(3 : ℝ))^2 := by nlinarith [sourceSampling_max_height stage,Real.rpow_nonneg (sourceBlockSize_pos stage).le (3 : ℝ)]
      _ = _ := by dsimp [m]; rw [← Real.rpow_natCast,← Real.rpow_mul (sourceBlockSize_pos stage).le]; norm_num
  apply hb.trans
  change (4*(26*m^(-80 : ℝ)))*C^2 ≤ 104*m^(-74 : ℝ)
  calc
    _ ≤ (4*(26*m^(-80 : ℝ)))*m^(6 : ℝ) := mul_le_mul_of_nonneg_left hC2 (by positivity)
    _ = _ := by rw [mul_assoc, mul_assoc,← Real.rpow_add (sourceBlockSize_pos stage)]; norm_num; ring

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceSampling_second_pair_error_oai := @OAI.FiniteFactor.sourceSampling_second_pair_error_oai
