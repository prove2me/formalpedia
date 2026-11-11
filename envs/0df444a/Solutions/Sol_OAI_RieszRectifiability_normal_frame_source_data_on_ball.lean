-- Prove2me | solution 1 for OAI.RieszRectifiability.normal_frame_source_data_on_ball
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:54.392874+00:00
-- url     : https://prove2.me/submissions/6b843f13-811c-4cf9-bf21-733ce627c8c3

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

theorem kernel_antisymm {d : ℕ} (n : ℕ) (x y : Ambient d) :
    kernel n y x = -kernel n x y := by
  rw [kernel, kernel, norm_sub_rev, ← neg_sub x y, smul_neg]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_KernelBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Elementary measurability and inverse-distance bounds for the Euclidean Riesz kernel.
Global upper growth records the ball-mass estimate used in kernel integration.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem kernel_measurable_right {d : ℕ} (n : ℕ) (x : Ambient d) :
    Measurable (kernel n x) := by
  have : IsBoundedSMul ℝ (Ambient d) := NormedSpace.toIsBoundedSMul
  have : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have : MeasurableSMul₂ ℝ (Ambient d) := ContinuousSMul.measurableSMul₂
  unfold kernel
  fun_prop

theorem kernel_norm_of_ne {d : ℕ} (n : ℕ) (x y : Ambient d) (hxy : x ≠ y) :
    ‖kernel n x y‖ = (dist x y ^ n)⁻¹ := by
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hnonneg : 0 ≤ (‖x - y‖ ^ (n + 1))⁻¹ := by positivity
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, dist_eq_norm, pow_succ]
  field_simp

theorem kernel_norm_le_truncation {d : ℕ} (n : ℕ) (x y : Ambient d)
    (ε : ℝ) (hε : 0 < ε) (hy : ε ≤ dist x y) :
    ‖kernel n x y‖ ≤ (ε ^ n)⁻¹ := by
  have hd : 0 < dist x y := lt_of_lt_of_le hε hy
  rw [kernel_norm_of_ne n x y (dist_pos.mp hd)]
  simpa only [one_div] using!
    one_div_le_one_div_of_le (pow_pos hε n) (pow_le_pow_left₀ hε.le hy n)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Flatness_OpenPlaneBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Open projection boxes and coordinate-plane measures

Pulling back open boxes along continuous coordinates gives open subsets of the
ambient space. Coordinate-plane measures satisfy upper growth bounds, which
in turn imply finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem GlobalUpperGrowth.finite_on_compacts {d n : ℕ} {C : ℝ}
    {μ : Measure (Ambient d)} (h : GlobalUpperGrowth n C μ) : IsFiniteMeasureOnCompacts μ := by
  let : IsLocallyFiniteMeasure μ := ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num),
    (h.2 x 1 (by norm_num)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_EnergyIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem centered_coordinate_difference (u v c : ℝ) :
    (u - c) - (v - c) = u - v := by
  ring

theorem normal_coordinate_difference {d : ℕ} (e z x y : Ambient d) :
    inner ℝ e (x - z) - inner ℝ e (y - z) = inner ℝ e (x - y) := by
  simp only [inner_sub_right]
  ring

theorem cutoff_square_eq_pairing_add_error (u v a b : ℝ) :
    (a * u - b * v) ^ 2 =
      (u - v) * (a ^ 2 * u - b ^ 2 * v) + u * v * (a - b) ^ 2 := by
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_CellEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

variable [MetricSpace X]

omit [MeasurableSpace X] in
theorem fractionalPairEnergy_nonneg (m : ℕ) (w : X → ℝ) (x y : X) :
    0 ≤ fractionalPairEnergy m w x y := by
  unfold fractionalPairEnergy
  positivity

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteStepLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-step functions in L²

Finite-step functions on finite measures belong to L². Products are represented on
intersections of cells, expressing squared distances through cell masses and mixed moments.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem toLp_norm_sq_eq_integral (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_L2Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral pairings of real L² functions

The L² inner product agrees with integration of pointwise products. Subtraction and
Cauchy–Schwarz then bound differences of pairings by squared L² errors.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X : Type*} [MeasurableSpace X]

theorem real_scalar_inner_mul (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  simp only [← pow_two, Real.norm_eq_abs, sq_abs]
  ring

theorem toLp_inner_eq_integral (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy, real_scalar_inner_mul]

theorem integral_mul_cauchy_schwarz_sq (μ : Measure X) (f g : X → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [toLp_norm_sq_eq_integral, toLp_norm_sq_eq_integral] at h
  simpa only [toLp_inner_eq_integral, pow_two] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BallLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localization to balls

Restricting a measure preserves its global upper growth bound and gives finite mass on
positive-radius balls. The diameter estimate controls pairs of points in a ball, while
the Lipschitz height estimate supplies the boundedness needed for local `MemLp` control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem globalGrowth_restrict {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (s : Set (Ambient d)) :
    GlobalUpperGrowth m C (μ.restrict s) := by
  refine ⟨hg.1, fun a R hR => ?_⟩
  exact (Measure.restrict_le_self (s := s) (μ := μ) (ball a R)).trans (hg.2 a R hR)

theorem finiteMeasure_restrict_ball_of_globalGrowth {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) : IsFiniteMeasure (μ.restrict (ball a R)) := by
  constructor
  simpa only [Measure.restrict_apply_univ] using! (hg.2 a R hR).trans_lt ENNReal.ofReal_lt_top

theorem ball_restriction_mass_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    (μ.restrict (ball a R)).real univ ≤ C * R ^ m := by
  simpa only [Measure.real, Measure.restrict_apply_univ] using!
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity)) (hg.2 a R hR)

theorem ball_restriction_pair_diameter {d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (R : ℝ)
    [SFinite (μ.restrict (ball a R))] :
    ∀ᵐ q ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)), dist q.1 q.2 ≤ 2 * R := by
  have hs : ∀ᵐ x ∂μ.restrict (ball a R), x ∈ ball a R := ae_restrict_mem measurableSet_ball
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
    Measure.quasiMeasurePreserving_snd.ae hs] with q hx hy
  change dist q.1 a < R at hx
  change dist q.2 a < R at hy
  have ht := dist_triangle q.1 a q.2
  rw [dist_comm a q.2] at ht
  linarith

theorem lipschitz_height_bound_on_ball {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a x : Ambient d) (R : ℝ) (hx : x ∈ ball a R) :
    |w x| ≤ |w a| + (K : ℝ) * R := by
  have hdiff : |w x - w a| ≤ (K : ℝ) * dist x a := by
    simpa only [Real.dist_eq] using! hw.dist_le_mul x a
  have habs : |w x| ≤ |w x - w a| + |w a| := by
    simpa only [sub_zero] using! abs_sub_le (w x) (w a) 0
  have hprod := mul_le_mul_of_nonneg_left hx.le K.coe_nonneg
  linarith

theorem lipschitz_height_memLp_on_ball {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    MemLp w 2 (μ.restrict (ball a R)) := by
  have := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable (|w a| + (K : ℝ) * R)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simpa only [Real.norm_eq_abs] using! lipschitz_height_bound_on_ball w K hw a x R hx

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NearPairWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem nearPairSet_measurable {d : ℕ} (r : ℝ) :
    MeasurableSet (nearPairSet (d := d) r) :=
  measurableSet_le (continuous_snd.dist continuous_fst).measurable measurable_const

theorem nearPairWeight_measurable {d : ℕ} (p : ℕ) (r : ℝ) :
    Measurable (nearPairWeight (d := d) p r) := by
  apply Measurable.indicator _ (nearPairSet_measurable r)
  unfold inverseDistancePow
  fun_prop

theorem nearPairWeight_nonneg {d : ℕ} (p : ℕ) (r : ℝ) (q : Ambient d × Ambient d) :
    0 ≤ nearPairWeight p r q :=
  indicator_nonneg (fun _ _ => inverseDistancePow_nonneg p _ _) q

theorem nearPairWeight_section {d : ℕ} (p : ℕ) (r : ℝ) (x : Ambient d) :
    (fun y => nearPairWeight p r (x, y)) =
      (closedBall x r).indicator (inverseDistancePow p x) := by
  funext y
  classical
  by_cases h : y ∈ closedBall x r
  · simp only [nearPairWeight, indicator_of_mem (show (x, y) ∈ nearPairSet r from h),
      indicator_of_mem h]
  · simp only [nearPairWeight, indicator_of_notMem (show (x, y) ∉ nearPairSet r from h),
      indicator_of_notMem h]

theorem nearPairWeight_section_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    Integrable (fun y => nearPairWeight p r (x, y)) μ := by
  rw [nearPairWeight_section]
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (inverseDistancePow_near_integrable_and_bound p C μ hg x r hr).1

theorem nearPairWeight_section_norm_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    (∫ y, ‖nearPairWeight p r (x, y)‖ ∂μ) ≤ 2 * (C * 2 ^ (p + 1) * 2 ^ p * r) := by
  simp_rw [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)]
  rw [nearPairWeight_section, integral_indicator measurableSet_closedBall]
  exact inverseDistancePow_near_integral_bound p C μ hg x r hr

theorem nearPairWeight_integrable {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (r : ℝ) (hr : 0 < r) : Integrable (nearPairWeight p r) (μ.prod μ) := by
  have hmeas : AEStronglyMeasurable (nearPairWeight p r) (μ.prod μ) :=
    (nearPairWeight_measurable p r).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).mpr
  refine ⟨Filter.Eventually.of_forall (nearPairWeight_section_integrable p C μ hg r hr), ?_⟩
  apply Integrable.of_bound hmeas.norm.integral_prod_right' (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact nearPairWeight_section_norm_bound p C μ hg r hr x

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricKernelL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Function Set

variable {X : Type*} [MeasurableSpace X]

theorem row_weighted_square_integrable_and_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q)
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) ∧
      (∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ) ≤ B * (∫ x, w x ^ 2 ∂μ) := by
  have hm : AEStronglyMeasurable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) := by
    fun_prop
  have hi : Integrable (fun q : X × X => w q.1 ^ 2 * k q) (μ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (fun x => (hrow x).const_mul (w x ^ 2)), ?_⟩
    apply (hL2.integrable_sq.const_mul B).mono' hm.norm.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hk0 _)), integral_const_mul]
    simpa only [mul_comm B] using! mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (w x))
  refine ⟨hi, ?_⟩
  have houter := hi.integral_prod_left
  simp only [integral_const_mul] at houter
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ x, B * w x ^ 2 ∂μ :=
      integral_mono houter (hL2.integrable_sq.const_mul B) (fun x => by
        simpa only [mul_comm B] using! mul_le_mul_of_nonneg_left (hB x) (sq_nonneg (w x)))
    _ = _ := integral_const_mul _ _

theorem symmetric_weight_product_integrable_and_bound
    (μ : Measure X) [IsFiniteMeasure μ] (k : X × X → ℝ)
    (hk : Measurable k) (hk0 : ∀ q, 0 ≤ k q)
    (hsymm : ∀ x y, k (y, x) = k (x, y))
    (hrow : ∀ x, Integrable (fun y => k (x, y)) μ)
    (B : ℝ) (hB : ∀ x, (∫ y, k (x, y) ∂μ) ≤ B)
    (w : X → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ) :
    Integrable (fun q : X × X => |w q.1 * w q.2| * k q) (μ.prod μ) ∧
      (∫ q : X × X, |w q.1 * w q.2| * k q ∂μ.prod μ) ≤
        B * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨hi₁, hb₁⟩ := row_weighted_square_integrable_and_bound μ k hk hk0 hrow B hB w hw hL2
  have hswap (q : X × X) : k q.swap = k q := hsymm q.1 q.2
  have hi₂ : Integrable (fun q : X × X => w q.2 ^ 2 * k q) (μ.prod μ) := by
    simpa only [Function.comp_def, Prod.fst_swap, hswap] using! hi₁.swap
  have heq : (∫ q : X × X, w q.2 ^ 2 * k q ∂μ.prod μ) =
      ∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ := by
    simpa only [Prod.fst_swap, hswap] using!
      (integral_prod_swap (μ := μ) (ν := μ) (fun q : X × X => w q.1 ^ 2 * k q))
  have hpoint (q : X × X) : |w q.1 * w q.2| * k q ≤
      (w q.1 ^ 2 * k q + w q.2 ^ 2 * k q) / 2 := by
    have h : 2 * |w q.1 * w q.2| ≤ w q.1 ^ 2 + w q.2 ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|w q.1| - |w q.2|), sq_abs (w q.1), sq_abs (w q.2)]
    have := mul_le_mul_of_nonneg_right h (hk0 q)
    nlinarith
  have hi : Integrable (fun q : X × X => |w q.1 * w q.2| * k q) (μ.prod μ) := by
    apply ((hi₁.add hi₂).div_const 2).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hk0 q))]
      exact hpoint q)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q : X × X, (w q.1 ^ 2 * k q + w q.2 ^ 2 * k q) / 2 ∂μ.prod μ :=
      integral_mono hi ((hi₁.add hi₂).div_const 2) hpoint
    _ = ∫ q : X × X, w q.1 ^ 2 * k q ∂μ.prod μ := by
      rw [integral_div, integral_add hi₁ hi₂, heq]
      ring
    _ ≤ _ := hb₁

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Rigidity_FractionalBilinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function
open scoped NNReal

variable {d : ℕ}

theorem weightedDifference_measurable (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w) :
    Measurable (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) := by
  unfold weightedDifference
  fun_prop

theorem weightedDifference_sq (m : ℕ) (w : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y ^ 2 = fractionalPairEnergy m w x y := by
  rw [weightedDifference, div_pow, Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem weightedDifference_mul (m : ℕ) (w ψ : Ambient d → ℝ) (x y : Ambient d) :
    weightedDifference m w x y * weightedDifference m ψ x y = fractionalBilinear m w ψ x y := by
  rw [weightedDifference, weightedDifference, div_mul_div_comm, ← pow_two,
    Real.sq_sqrt (pow_nonneg dist_nonneg _)]
  rfl

theorem lipschitz_fractionalEnergy_bound (p : ℕ) (ψ : Ambient d → ℝ)
    (L : ℝ≥0) (hψ : LipschitzWith L ψ) (x y : Ambient d) :
    fractionalPairEnergy (p + 1) ψ x y ≤ (L : ℝ) ^ 2 * (dist x y ^ p)⁻¹ := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    positivity
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hdiff : |ψ x - ψ y| ≤ (L : ℝ) * dist x y := by
      simpa only [Real.dist_eq] using! hψ.dist_le_mul x y
    have hsq : (ψ x - ψ y) ^ 2 ≤ (L : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg)).mpr hdiff
    calc
      _ ≤ ((L : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        field_simp

theorem weightedDifference_memLp (m : ℕ) (w : Ambient d → ℝ) (hw : Measurable w)
    (ρ : Measure (Ambient d × Ambient d))
    (hE : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) ρ) :
    MemLp (fun q : Ambient d × Ambient d => weightedDifference m w q.1 q.2) 2 ρ := by
  apply (memLp_two_iff_integrable_sq (weightedDifference_measurable m w hw).aestronglyMeasurable).mpr
  simpa only [weightedDifference_sq] using! hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CutoffError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted fractional cutoff errors

The cutoff error weights the fractional pair energy at both endpoints. Symmetry of the
near-pair weight supports integrability and bounds for the contribution of nearby pairs.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem nearPairWeight_swap {d : ℕ} (p : ℕ) (r : ℝ) (x y : Ambient d) :
    nearPairWeight p r (y, x) = nearPairWeight p r (x, y) := by
  classical
  have hmem : (y, x) ∈ nearPairSet r ↔ (x, y) ∈ nearPairSet r := by
    simp only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm]
  by_cases h : (x, y) ∈ nearPairSet r
  · simp only [nearPairWeight, indicator_of_mem h, indicator_of_mem (hmem.mpr h),
      inverseDistancePow, dist_comm]
  · simp only [nearPairWeight, indicator_of_notMem h,
      indicator_of_notMem (mt hmem.mp h)]

theorem near_cutoffError_integrable_and_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2)
      (nearPairSet r) (μ.prod μ) ∧
      (∫ q in nearPairSet r, |cutoffError (p + 1) w χ q.1 q.2| ∂μ.prod μ) ≤
        (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨hi, hb⟩ := symmetric_weight_product_integrable_and_bound μ
    (nearPairWeight p r) (nearPairWeight_measurable p r) (nearPairWeight_nonneg p r)
    (nearPairWeight_swap p r) (nearPairWeight_section_integrable p C μ hg r hr)
    (2 * (C * 2 ^ (p + 1) * 2 ^ p * r))
    (fun x => by simpa only [Real.norm_of_nonneg (nearPairWeight_nonneg p r _)] using!
      nearPairWeight_section_norm_bound p C μ hg r hr x) w hw hL2
  have hχm : Measurable χ := hχ.continuous.measurable
  have hm : Measurable (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2) := by
    unfold cutoffError fractionalPairEnergy
    fun_prop
  have hdom (q : Ambient d × Ambient d) (hq : q ∈ nearPairSet r) :
      |cutoffError (p + 1) w χ q.1 q.2| ≤
        (L : ℝ) ^ 2 * (|w q.1 * w q.2| * nearPairWeight p r q) := by
    rw [cutoffError, abs_mul, abs_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _),
      nearPairWeight, indicator_of_mem hq]
    have h := mul_le_mul_of_nonneg_left
      (lipschitz_fractionalEnergy_bound p χ L hχ q.1 q.2) (abs_nonneg (w q.1 * w q.2))
    simpa only [inverseDistancePow, mul_left_comm] using! h
  have hI : IntegrableOn (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2)
      (nearPairSet r) (μ.prod μ) := by
    apply (hi.const_mul ((L : ℝ) ^ 2)).restrict.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (nearPairSet_measurable r)] with q hq
    simpa only [Real.norm_eq_abs] using! hdom q hq
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ q in nearPairSet r,
        (L : ℝ) ^ 2 * (|w q.1 * w q.2| * nearPairWeight p r q) ∂μ.prod μ := by
      apply integral_mono_ae hI.abs (hi.const_mul ((L : ℝ) ^ 2)).restrict
      filter_upwards [ae_restrict_mem (nearPairSet_measurable r)] with q hq
      exact hdom q hq
    _ ≤ ∫ q : Ambient d × Ambient d,
        (L : ℝ) ^ 2 * (|w q.1 * w q.2| * nearPairWeight p r q) ∂μ.prod μ :=
      setIntegral_le_integral (hi.const_mul ((L : ℝ) ^ 2))
        (Filter.Eventually.of_forall fun q => by
          exact mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (nearPairWeight_nonneg p r q)))
    _ ≤ (L : ℝ) ^ 2 * ((2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ)) := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CutoffEnergyIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integral estimates for cutoff energies

Bounded multipliers preserve the square-integrability needed for cutoff estimates. An
almost-everywhere diameter bound makes the near-pair error estimate global, while the
fractional energy identity separates the bilinear contribution from the cutoff error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem bounded_multiplier_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w χ : X → ℝ) (hw : Measurable w) (hχ : Measurable χ)
    (hL2 : MemLp w 2 μ) (H : ℝ) (hH : ∀ᵐ x ∂μ, ‖χ x‖ ≤ H) :
    MemLp (fun x => χ x * w x) 2 μ := by
  apply (hL2.norm.const_mul H).mono' ((hχ.mul hw).aestronglyMeasurable)
  filter_upwards [hH] with x hx
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem cutoffError_integrable_and_bound_of_ae_diameter {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ) (r : ℝ) (hr : 0 < r)
    (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d, |cutoffError (p + 1) w χ q.1 q.2| ∂μ.prod μ) ≤
        (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  have hmem : ∀ᵐ q ∂μ.prod μ, q ∈ nearPairSet r := by
    simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hdiam
  have heq := Measure.restrict_eq_self_of_ae_mem hmem
  simpa only [IntegrableOn, heq] using!
    near_cutoffError_integrable_and_bound p C μ hg w χ hw hL2 L hχ r hr

theorem cutoff_fractionalEnergy_identity {d : ℕ} (m : ℕ)
    (w χ : Ambient d → ℝ) (x y : Ambient d) :
    fractionalPairEnergy m (fun z => χ z * w z) x y =
      fractionalBilinear m w (fun z => χ z ^ 2 * w z) x y + cutoffError m w χ x y := by
  simpa only [fractionalPairEnergy, fractionalBilinear, cutoffError, add_div, mul_div_assoc] using!
    congrArg (fun t : ℝ => t / dist x y ^ (m + 1))
      (cutoff_square_eq_pairing_add_error (w x) (w y) (χ x) (χ y))

theorem cutoff_energy_from_integrable_interior_pairing {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r)
    (hpair : Integrable (fun q : Ambient d × Ambient d =>
      fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2) (μ.prod μ))
    (A : ℝ) (hA : (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂μ.prod μ) ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2 ∂μ.prod μ) ≤
        A + (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨herr, herrorBound⟩ := cutoffError_integrable_and_bound_of_ae_diameter
    p C μ hg w χ hw hL2 L hχ r hr hdiam
  constructor
  · simpa only [cutoff_fractionalEnergy_identity] using! hpair.add herr
  · simp_rw [cutoff_fractionalEnergy_identity]
    rw [integral_add hpair herr]
    exact add_le_add hA ((integral_mono herr herr.abs (fun _ => le_abs_self _)).trans herrorBound)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ShellHeightL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# First-moment bounds on dyadic shells

Cauchy–Schwarz bounds an absolute first moment by the mass and second moment of
a finite measure. Applying this estimate to dyadic annuli combines upper growth
with shellwise second-moment decay to control the corresponding height integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem integral_abs_sq_le_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν) :
    (∫ x, |w x| ∂ν) ^ 2 ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := by
  have h := integral_mul_cauchy_schwarz_sq ν (fun x => ‖w x‖) (fun _ => (1 : ℝ))
    hw.norm (memLp_const 1)
  simpa only [mul_one, one_mul, one_pow, integral_const, smul_eq_mul, Real.norm_eq_abs,
    sq_abs, mul_comm] using! h

theorem integral_abs_le_of_mass_second_moment {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w : X → ℝ) (hw : MemLp w 2 ν)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M * A ^ 2) :
    (∫ x, |w x| ∂ν) ≤ M * A := by
  have hsq : (∫ x, |w x| ∂ν) ^ 2 ≤ (M * A) ^ 2 := by
    calc
      _ ≤ ν.real univ * (∫ x, w x ^ 2 ∂ν) := integral_abs_sq_le_mass_second_moment ν w hw
      _ ≤ M * (M * A ^ 2) := mul_le_mul hmass hsecond
        (integral_nonneg fun x => sq_nonneg _) hM
      _ = _ := by ring
  exact (sq_le_sq₀ (integral_nonneg fun x => abs_nonneg _) (mul_nonneg hM hA)).mp hsq

theorem shell_height_l1_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (w : Ambient d → ℝ) (hw : MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsecond : (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    (∫ y in dyadicAnnulus a R k, |w y| ∂μ) ≤
      B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k := by
  let ν := μ.restrict (dyadicAnnulus a R k)
  have : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hmass : ν.real univ ≤ B * (R * 2 ^ k) ^ m := by
    have hmass' : μ.real (dyadicAnnulus a R k) ≤ C * (R * 2 ^ (k + 1)) ^ m :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
        ((measure_mono (dyadicAnnulus_subset_ball a R k)).trans (hg.2 a _ (by positivity)))
    have heq : C * (R * (2 : ℝ) ^ (k + 1)) ^ m = (C * 2 ^ m) * (R * 2 ^ k) ^ m := by
      rw [pow_succ, show R * ((2 : ℝ) ^ k * 2) = (R * 2 ^ k) * 2 by ring, mul_pow]
      ring
    change (μ.restrict (dyadicAnnulus a R k)).real univ ≤ _
    simpa only [Measure.real, Measure.restrict_apply_univ] using!
      hmass'.trans (heq ▸ mul_le_mul_of_nonneg_right hCB (by positivity))
  have h := integral_abs_le_of_mass_second_moment ν w hw
    (B * (R * 2 ^ k) ^ m) (δ * (R * 2 ^ k) * b ^ k) (by positivity) (by positivity) hmass hsecond
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CutoffTestMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Moments of squared-cutoff tests

A cutoff bounded by one preserves square-integrability when its square multiplies a test
function. Hölder integrability and pointwise domination then control the first moment of
this test and its pairing with the original function.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem cutoff_square_le_one {X : Type*} (χ : X → ℝ)
    (hχ : ∀ x, |χ x| ≤ 1) (x : X) : χ x ^ 2 ≤ 1 := by
  simpa only [sq_abs, one_pow] using! pow_le_pow_left₀ (abs_nonneg (χ x)) (hχ x) 2

theorem squared_cutoff_test_memLp {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (w χ : X → ℝ) (hw : Measurable w) (hχ : Measurable χ)
    (hL2 : MemLp w 2 ν) (hbound : ∀ x, |χ x| ≤ 1) :
    MemLp (fun x => χ x ^ 2 * w x) 2 ν := by
  apply bounded_multiplier_memLp ν w (fun x => χ x ^ 2) hw (hχ.pow_const 2) hL2 1
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact cutoff_square_le_one χ hbound x

theorem squared_cutoff_test_moment_bounds {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (w χ : X → ℝ)
    (hw : Measurable w) (hχ : Measurable χ) (hL2 : MemLp w 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, w x ^ 2 ∂ν) ≤ M * δ ^ 2) :
    Integrable (fun x => χ x ^ 2 * w x) ν ∧
      Integrable (fun x => (χ x ^ 2 * w x) * w x) ν ∧
      (∫ x, |χ x ^ 2 * w x| ∂ν) ≤ M * δ ∧
      (∫ x, |(χ x ^ 2 * w x) * w x| ∂ν) ≤ M * δ ^ 2 := by
  have htestL2 := squared_cutoff_test_memLp ν w χ hw hχ hL2 hbound
  have htest := htestL2.integrable (by norm_num)
  have hprodLp : MemLp (fun x => (χ x ^ 2 * w x) * w x) 1 ν := MemLp.mul' (hφ := htestL2) (hf := hL2)
  have hprod := memLp_one_iff_integrable.mp hprodLp
  refine ⟨htest, hprod, ?_, ?_⟩
  · calc
      _ ≤ ∫ x, |w x| ∂ν := by
        apply integral_mono htest.abs (hL2.integrable (by norm_num)).abs
        intro x
        change |χ x ^ 2 * w x| ≤ |w x|
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right (cutoff_square_le_one χ hbound x) (abs_nonneg (w x))
      _ ≤ _ := integral_abs_le_of_mass_second_moment ν w hL2 M δ hM hδ hmass hsecond
  · calc
      _ ≤ ∫ x, w x ^ 2 ∂ν := by
        apply integral_mono hprod.abs hL2.integrable_sq
        intro x
        change |(χ x ^ 2 * w x) * w x| ≤ w x ^ 2
        have heq : |(χ x ^ 2 * w x) * w x| = χ x ^ 2 * w x ^ 2 := by
          rw [mul_assoc, ← pow_two, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
        rw [heq]
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right (cutoff_square_le_one χ hbound x) (sq_nonneg (w x))
      _ ≤ _ := hsecond

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LipschitzTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

theorem lipschitz_bounded_product_real {f g : X → ℝ} {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  calc
    dist (f x * g x) (f y * g y) =
        |f x * (g x - g y) + (f x - f y) * g y| := by
      rw [Real.dist_eq]
      congr 1
      ring
    _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
      simpa only [abs_mul] using! abs_add_le
        (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) +
        ((Kf : ℝ) * dist x y) * (Bg : ℝ) := by
      exact add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
        (mul_le_mul hf' (hBg y) (abs_nonneg _) (by positivity))
    _ = ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
      simp only [NNReal.coe_add, NNReal.coe_mul]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalLipschitzEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local Lipschitz control of fractional energy

Almost-everywhere Lipschitz difference bounds and bounded pair distances give
integrability of fractional pair energies under global upper growth. Their weighted
differences lie in L², yielding integrability of the associated bilinear pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem fractionalEnergy_bound_of_difference_bound {d : ℕ} (p : ℕ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (x y : Ambient d)
    (h : |w x - w y| ≤ (K : ℝ) * dist x y) :
    fractionalPairEnergy (p + 1) w x y ≤ (K : ℝ) ^ 2 * inverseDistancePow p x y := by
  by_cases hxy : x = y
  · subst y
    simp only [fractionalPairEnergy, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    exact mul_nonneg (sq_nonneg _) (inverseDistancePow_nonneg _ _ _)
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    have hsq : (w x - w y) ^ 2 ≤ (K : ℝ) ^ 2 * dist x y ^ 2 := by
      simpa only [sq_abs, mul_pow] using!
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg K.coe_nonneg dist_nonneg)).mpr h
    calc
      _ ≤ ((K : ℝ) ^ 2 * dist x y ^ 2) / dist x y ^ (p + 1 + 1) :=
        div_le_div_of_nonneg_right hsq (pow_nonneg dist_nonneg _)
      _ = _ := by
        rw [show p + 1 + 1 = p + 2 by omega, pow_add]
        unfold inverseDistancePow
        field_simp

theorem fractionalEnergy_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w : Ambient d → ℝ) (hw : Measurable w) (K : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) w q.1 q.2)
      (μ.prod μ) := by
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) w q.1 q.2) := by
    unfold fractionalPairEnergy
    fun_prop
  apply ((nearPairWeight_integrable p C μ hg r hr).const_mul ((K : ℝ) ^ 2)).mono'
    hm.aestronglyMeasurable
  filter_upwards [hK, hdiam] with q hq hd
  have hmem : q ∈ nearPairSet r := by
    simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hd
  rw [Real.norm_of_nonneg (fractionalPairEnergy_nonneg _ _ _ _), nearPairWeight,
    indicator_of_mem hmem]
  exact fractionalEnergy_bound_of_difference_bound p w K q.1 q.2 hq

theorem fractionalBilinear_integrable_of_ae_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w ψ : Ambient d → ℝ) (hw : Measurable w) (hψ : Measurable ψ) (K L : ℝ≥0)
    (hK : ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2)
    (hL : ∀ᵐ q ∂μ.prod μ, |ψ q.1 - ψ q.2| ≤ (L : ℝ) * dist q.1 q.2)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) w ψ q.1 q.2)
      (μ.prod μ) := by
  have hf := weightedDifference_memLp (p + 1) w hw (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg w hw K hK r hr hdiam)
  have hgtest := weightedDifference_memLp (p + 1) ψ hψ (μ.prod μ)
    (fractionalEnergy_integrable_of_ae_lipschitz p C μ hg ψ hψ L hL r hr hdiam)
  have hprod : MemLp (fun q : Ambient d × Ambient d =>
      weightedDifference (p + 1) w q.1 q.2 * weightedDifference (p + 1) ψ q.1 q.2)
      1 (μ.prod μ) := MemLp.mul' (hφ := hf) (hf := hgtest)
  simpa only [weightedDifference_mul] using! memLp_one_iff_integrable.mp hprod

theorem ae_difference_bound_of_lipschitzOn {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (s : Set (Ambient d))
    (hs : ∀ᵐ x ∂μ, x ∈ s) (w : Ambient d → ℝ) (K : ℝ≥0) (hK : LipschitzOnWith K w s) :
    ∀ᵐ q ∂μ.prod μ, |w q.1 - w q.2| ≤ (K : ℝ) * dist q.1 q.2 := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hs,
    Measure.quasiMeasurePreserving_snd.ae hs] with q hx hy
  simpa only [Real.dist_eq] using! hK.dist_le_mul q.1 hx q.2 hy

theorem lipschitzOn_bounded_product_real {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (f g : X → ℝ) (Kf Kg Bf Bg : ℝ≥0)
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hBf : ∀ x ∈ s, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x ∈ s, |g x| ≤ (Bg : ℝ)) :
    LipschitzOnWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) s := by
  apply lipschitzOnWith_iff_restrict.mpr
  exact lipschitz_bounded_product_real (lipschitzOnWith_iff_restrict.mp hf)
    (lipschitzOnWith_iff_restrict.mp hg) (fun x => hBf x x.property) (fun x => hBg x x.property)

theorem squared_cutoff_height_lipschitzOn {d : ℕ}
    (s : Set (Ambient d)) (w χ : Ambient d → ℝ) (K L W H : ℝ≥0)
    (hw : LipschitzOnWith K w s) (hχ : LipschitzOnWith L χ s)
    (hW : ∀ x ∈ s, |w x| ≤ (W : ℝ)) (hH : ∀ x ∈ s, |χ x| ≤ (H : ℝ)) :
    LipschitzOnWith (H * (H * K + L * W) + L * (H * W))
      (fun x => χ x ^ 2 * w x) s := by
  have hprod := lipschitzOn_bounded_product_real s χ w L K H W hχ hw hH hW
  have hbound (x : Ambient d) (hx : x ∈ s) : |χ x * w x| ≤ ((H * W : ℝ≥0) : ℝ) := by
    rw [abs_mul, NNReal.coe_mul]
    exact mul_le_mul (hH x hx) (hW x hx) (abs_nonneg _) H.coe_nonneg
  have h := lipschitzOn_bounded_product_real s χ (fun x => χ x * w x)
    L (H * K + L * W) H (H * W) hχ hprod hH hbound
  simpa only [pow_two, mul_assoc] using! h

theorem localized_cutoff_energy_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (s : Set (Ambient d)) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (K L W H : ℝ≥0) (hwLip : LipschitzOnWith K w s) (hχ : LipschitzWith L χ)
    (hW : ∀ x ∈ s, |w x| ≤ (W : ℝ)) (hH : ∀ x ∈ s, |χ x| ≤ (H : ℝ))
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r)
    (A : ℝ) (hA : (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂μ.prod μ) ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2 ∂μ.prod μ) ≤
        A + (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  have htest := squared_cutoff_height_lipschitzOn s w χ K L W H hwLip hχ.lipschitzOnWith hW hH
  have hmtest : Measurable (fun x => χ x ^ 2 * w x) :=
    (hχ.continuous.measurable.pow_const 2).mul hw
  apply cutoff_energy_from_integrable_interior_pairing p C μ hg w χ hw hL2 L hχ r hr hdiam
  · exact fractionalBilinear_integrable_of_ae_lipschitz p C μ hg w (fun x => χ x ^ 2 * w x)
      hw hmtest K (H * (H * K + L * W) + L * (H * W))
      (ae_difference_bound_of_lipschitzOn μ s hs w K hwLip)
      (ae_difference_bound_of_lipschitzOn μ s hs _ _ htest) r hr hdiam
  · exact hA

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarKernelDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem inverseDistancePow_far_difference {d : ℕ} (m : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * dist x a * inverseDistancePow (m + 2) a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  have h := inverse_pow_difference_le m (dist x y) (dist a y) (dist a y / 2)
    (by positivity) hhalf (by linarith)
  have hdist := abs_dist_sub_le x a y
  unfold inverseDistancePow
  calc
    _ ≤ (m + 1 : ℝ) * |dist x y - dist a y| * ((dist a y / 2) ^ (m + 2))⁻¹ := h
    _ ≤ (m + 1 : ℝ) * dist x a * ((dist a y / 2) ^ (m + 2))⁻¹ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdist (by positivity))
        (by positivity)
    _ = _ := by
      rw [div_pow, inv_div]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FarHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem lipschitz_height_radial_bound {d : ℕ} (w : Ambient d → ℝ)
    (K : ℝ≥0) (hw : LipschitzWith K w) (a y : Ambient d) (R : ℝ)
    (hR : 0 < R) (hy : R ≤ dist a y) :
    |w y| ≤ ((K : ℝ) + |w a| / R) * dist a y := by
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have hconstant : |w a| ≤ (|w a| / R) * dist a y := by
    have h := mul_le_mul_of_nonneg_left hy (div_nonneg (abs_nonneg (w a)) hR.le)
    simpa only [div_mul_cancel₀ _ hR.ne'] using! h
  calc
    _ ≤ |w y - w a| + |w a| := by
      simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
    _ ≤ (K : ℝ) * dist a y + (|w a| / R) * dist a y := add_le_add hdiff hconstant
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_ClosedTailBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem closedExterior_measurable {d : ℕ} (a : Ambient d) (R : ℝ) :
    MeasurableSet (closedExterior a R) :=
  measurableSet_le measurable_const (continuous_const.dist continuous_id).measurable

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteShellTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted height bounds on dyadic shells

Square-integrable height bounds on each shell control integrals weighted by
inverse powers of distance. The dyadic coefficient identity expresses these
estimates in the geometric form needed for tail bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem dyadic_weighted_height_coefficient (m k : ℕ) (B δ R b : ℝ) (hR : 0 < R) :
    ((R * 2 ^ k) ^ (m + 2))⁻¹ * (B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k) =
      (B * δ / R) * (b / 2) ^ k := by
  rw [show m + 2 = (m + 1) + 1 by omega, pow_succ, div_pow]
  field_simp

theorem shell_weighted_height_integrable_and_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (w : Ambient d → ℝ) (hw : MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hsecond : (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (dyadicAnnulus a R k) μ ∧
      (∫ y in dyadicAnnulus a R k, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) * (b / 2) ^ k := by
  have : IsFiniteMeasure (μ.restrict (dyadicAnnulus a R k)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  have hfirst := (hw.integrable (by norm_num)).abs
  have hpoint : ∀ᵐ y ∂μ.restrict (dyadicAnnulus a R k),
      ‖inverseDistancePow (m + 2) a y‖ ≤ ((R * 2 ^ k) ^ (m + 2))⁻¹ := by
    filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable a R k)] with y hy
    exact inverseDistancePow_bound_on_annulus (m + 2) a R hR k y hy
  have hi := hfirst.mul_bdd (inverseDistancePow_measurable (m + 2) a).aestronglyMeasurable hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in dyadicAnnulus a R k, ((R * 2 ^ k) ^ (m + 2))⁻¹ * |w y| ∂μ := by
      apply integral_mono_ae hi (hfirst.const_mul _)
      filter_upwards [hpoint] with y hy
      rw [Real.norm_of_nonneg (inverseDistancePow_nonneg _ _ _)] at hy
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left hy (abs_nonneg (w y))
    _ = ((R * 2 ^ k) ^ (m + 2))⁻¹ * (∫ y in dyadicAnnulus a R k, |w y| ∂μ) :=
      integral_const_mul _ _
    _ ≤ ((R * 2 ^ k) ^ (m + 2))⁻¹ * (B * δ * (R * 2 ^ k) ^ (m + 1) * b ^ k) :=
      mul_le_mul_of_nonneg_left (shell_height_l1_bound m C B μ hg hCB a R hR k w hw δ b hδ hb hsecond)
        (by positivity)
    _ = _ := dyadic_weighted_height_coefficient m k B δ R b hR

theorem finiteShellRegion_eq {d : ℕ} (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    finiteShellRegion a R N = {y | R ≤ dist a y ∧ dist a y < R * 2 ^ N} := by
  ext y
  constructor
  · intro hy
    obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
    have hlow : R ≤ R * (2 : ℝ) ^ k := by
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
    have hhigh : R * (2 : ℝ) ^ (k + 1) ≤ R * 2 ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) hR.le
    exact ⟨hlow.trans hyk.1, hyk.2.trans_le hhigh⟩
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((closedExterior_subset_iUnion_dyadicAnnulus a R hR) hy.1)
    have hkN : k < N := by
      by_contra h
      have hp : R * (2 : ℝ) ^ N ≤ R * 2 ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt h)) hR.le
      exact (not_lt_of_ge (hp.trans hk.1)) hy.2
    exact mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkN, hk⟩

theorem finite_shell_weighted_height_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (w : Ambient d → ℝ) (hw : ∀ k < N, MemLp w 2 (μ.restrict (dyadicAnnulus a R k)))
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (finiteShellRegion a R N) μ ∧
      (∫ y in finiteShellRegion a R N, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) := by
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hI (k : ℕ) (hk : k ∈ Finset.range N) :=
    (shell_weighted_height_integrable_and_bound m C B μ hg hCB a R hR k w
      (hw k (Finset.mem_range.mp hk)) δ b hδ hb0 (hsecond k (Finset.mem_range.mp hk))).1
  have hratio : ‖b / 2‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; linarith
  have hgeo := summable_geometric_of_norm_lt_one hratio
  constructor
  · exact integrableOn_finset_iUnion.mpr hI
  · rw [finiteShellRegion, integral_biUnion_finset (Finset.range N)
      (fun k _ => dyadicAnnulus_measurable a R k)
      (fun k _ l _ hkl => dyadicAnnulus_disjoint a R hR hkl) hI]
    calc
      _ ≤ ∑ k ∈ Finset.range N, (B * δ / R) * (b / 2) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact (shell_weighted_height_integrable_and_bound m C B μ hg hCB a R hR k w
          (hw k (Finset.mem_range.mp hk)) δ b hδ hb0 (hsecond k (Finset.mem_range.mp hk))).2
      _ = (B * δ / R) * ∑ k ∈ Finset.range N, (b / 2) ^ k := by rw [Finset.mul_sum]
      _ ≤ (B * δ / R) * ∑' k : ℕ, (b / 2) ^ k :=
        mul_le_mul_of_nonneg_left (hgeo.sum_le_tsum (Finset.range N) (fun k _ => by positivity))
          (by positivity)
      _ = _ := by rw [tsum_geometric_of_norm_lt_one hratio]; rfl

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_HeightTailSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Annular integrability for height-tail estimates

Lipschitz height functions are bounded on each dyadic annulus. The finite
annular mass supplied by upper growth then gives the square integrability
needed to apply shell estimates in the height-tail decomposition.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem lipschitz_height_memLp_on_annulus {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (k : ℕ) :
    MemLp w 2 (μ.restrict (dyadicAnnulus a R k)) := by
  have : IsFiniteMeasure (μ.restrict (dyadicAnnulus a R k)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hR k⟩
  apply MemLp.of_bound hw.continuous.measurable.aestronglyMeasurable
    ((K : ℝ) * (R * 2 ^ (k + 1)) + |w a|)
  filter_upwards [ae_restrict_mem (dyadicAnnulus_measurable a R k)] with y hy
  rw [Real.norm_eq_abs]
  have hdiff : |w y - w a| ≤ (K : ℝ) * dist a y := by
    simpa only [Real.dist_eq, dist_comm y a] using! hw.dist_le_mul y a
  have habs : |w y| ≤ |w y - w a| + |w a| := by
    simpa only [sub_add_cancel] using! abs_add_le (w y - w a) (w a)
  exact habs.trans (add_le_add
    (hdiff.trans (mul_le_mul_of_nonneg_left hy.2.le K.coe_nonneg)) le_rfl)

theorem weighted_height_closed_tail_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        ((K : ℝ) + |w a| / R) * (2 * (C * 2 ^ m / R)) := by
  obtain ⟨hweight, hbound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hm : Measurable (fun y => |w y| * inverseDistancePow (m + 2) a y) :=
    hw.continuous.measurable.abs.mul (inverseDistancePow_measurable _ _)
  have hpoint (y : Ambient d) (hy : y ∈ closedExterior a R) :
      |w y| * inverseDistancePow (m + 2) a y ≤
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y := by
    have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
    calc
      _ ≤ (((K : ℝ) + |w a| / R) * dist a y) * inverseDistancePow (m + 2) a y :=
        mul_le_mul_of_nonneg_right (lipschitz_height_radial_bound w K hw a y R hR hy)
          (inverseDistancePow_nonneg _ _ _)
      _ = _ := by
        unfold inverseDistancePow
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        field_simp
  have hi : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ := by
    apply (hweight.const_mul ((K : ℝ) + |w a| / R)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (inverseDistancePow_nonneg _ _ _))]
    exact hpoint y hy
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y in closedExterior a R,
        ((K : ℝ) + |w a| / R) * inverseDistancePow (m + 1) a y ∂μ := by
      apply integral_mono_ae hi (hweight.const_mul _)
      filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
      exact hpoint y hy
    _ = ((K : ℝ) + |w a| / R) * (∫ y in closedExterior a R, inverseDistancePow (m + 1) a y ∂μ) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

theorem finiteShellRegion_union_closedExterior {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    finiteShellRegion a R N ∪ closedExterior a (R * 2 ^ N) = closedExterior a R := by
  rw [finiteShellRegion_eq a R hR N]
  have hRT : R ≤ R * (2 : ℝ) ^ N := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  ext y
  change (R ≤ dist a y ∧ dist a y < R * 2 ^ N) ∨ R * 2 ^ N ≤ dist a y ↔ R ≤ dist a y
  constructor
  · rintro (h | h)
    · exact h.1
    · exact hRT.trans h
  · intro hy
    by_cases h : dist a y < R * 2 ^ N
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (le_of_not_gt h)

theorem finiteShellRegion_disjoint_closedExterior {d : ℕ}
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    Disjoint (finiteShellRegion a R N) (closedExterior a (R * 2 ^ N)) := by
  rw [finiteShellRegion_eq a R hR N]
  exact Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hy) hx.2)

theorem improved_weighted_height_tail_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (δ b : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        (B * δ / R) / (1 - b / 2) +
          ((K : ℝ) + |w a| / (R * 2 ^ N)) * (2 * (C * 2 ^ m / (R * 2 ^ N))) := by
  obtain ⟨hIfin, hbfin⟩ := finite_shell_weighted_height_bound m C B μ hg hCB a R hR N w
    (fun k _ => lipschitz_height_memLp_on_annulus m C μ hg w K hw a R hR k) δ b hδ hb0 hb2 hsecond
  obtain ⟨hItail, hbtail⟩ := weighted_height_closed_tail_bound m C μ hg w K hw a (R * 2 ^ N) (by positivity)
  rw [← finiteShellRegion_union_closedExterior a R hR N]
  refine ⟨hIfin.union hItail, ?_⟩
  rw [setIntegral_union (finiteShellRegion_disjoint_closedExterior a R hR N)
    (closedExterior_measurable a (R * 2 ^ N)) hIfin hItail]
  exact add_le_add hbfin hbtail

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RenormalizedFarPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem inverseDistancePow_far_le {d : ℕ} (p : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    inverseDistancePow p x y ≤ 2 ^ p * inverseDistancePow p a y := by
  have hhalf : dist a y / 2 ≤ dist x y := by
    have ht := dist_triangle a x y
    rw [dist_comm a x] at ht
    linarith
  calc
    _ ≤ ((dist a y / 2) ^ p)⁻¹ := by
      simpa only [inverseDistancePow, one_div] using!
        one_div_le_one_div_of_le (pow_pos (by positivity : 0 < dist a y / 2) p)
          (pow_le_pow_left₀ (by positivity) hhalf p)
    _ = _ := by unfold inverseDistancePow; rw [div_pow, inv_div]; ring

theorem renormalizedNormalIntegrand_bound {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a x y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hx : dist x a ≤ H) (hy : R ≤ dist a y) :
    |renormalizedNormalIntegrand m w φ a (x, y)| ≤
      2 ^ (m + 1) * (|φ x * w x| * inverseDistancePow (m + 1) a y) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ x| * (|w y| * inverseDistancePow (m + 2) a y)) := by
  have hpos : 0 < dist a y := lt_of_lt_of_le hR hy
  have hfar : 2 * dist x a ≤ dist a y := (by linarith : 2 * dist x a ≤ R).trans hy
  have hk := inverseDistancePow_far_le (m + 1) a x y hpos hfar
  have hdiff : |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y| ≤
      (m + 1 : ℝ) * 2 ^ (m + 2) * H * inverseDistancePow (m + 2) a y := by
    apply (inverseDistancePow_far_difference m a x y hpos hfar).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity))
      (inverseDistancePow_nonneg _ _ _)
  unfold renormalizedNormalIntegrand
  rw [abs_mul]
  calc
    _ ≤ |φ x| * (|w x| * inverseDistancePow (m + 1) x y +
        |w y| * |inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y|) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (inverseDistancePow_nonneg _ _ _)] using!
        abs_sub_le (w x * inverseDistancePow (m + 1) x y) 0
          (w y * (inverseDistancePow (m + 1) x y - inverseDistancePow (m + 1) a y))
    _ ≤ |φ x| * (|w x| * (2 ^ (m + 1) * inverseDistancePow (m + 1) a y) +
        |w y| * ((m + 1 : ℝ) * 2 ^ (m + 2) * H * inverseDistancePow (m + 2) a y)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))) (abs_nonneg _)
    _ = _ := by rw [abs_mul]; ring

theorem renormalizedNormalIntegrand_bound_of_support {d : ℕ} (m : ℕ) (w φ : Ambient d → ℝ)
    (a x y : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hx : φ x ≠ 0 → dist x a ≤ H) (hy : R ≤ dist a y) :
    |renormalizedNormalIntegrand m w φ a (x, y)| ≤
      2 ^ (m + 1) * (|φ x * w x| * inverseDistancePow (m + 1) a y) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ x| * (|w y| * inverseDistancePow (m + 2) a y)) := by
  by_cases hφ : φ x = 0
  · simp only [renormalizedNormalIntegrand, hφ, zero_mul, abs_zero, mul_zero, add_zero, le_refl]
  · exact renormalizedNormalIntegrand_bound m w φ a x y H R hR hHR (hx hφ) hy

theorem renormalized_far_pairing_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (w φ : Ambient d → ℝ)
    (hw : Measurable w) (hφm : Measurable φ) (hφ : Integrable φ ν)
    (hφw : Integrable (fun x => φ x * w x) ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ)
    (Z : ℝ) (hZ : (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤ Z) :
    Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod (μ.restrict (closedExterior a R))) ∧
      (∫ q, |renormalizedNormalIntegrand m w φ a q| ∂ν.prod (μ.restrict (closedExterior a R))) ≤
        2 ^ (m + 1) * ((∫ x, |φ x * w x| ∂ν) * (2 * (C * 2 ^ m / R))) +
          ((m + 1 : ℝ) * 2 ^ (m + 2) * H) * ((∫ x, |φ x| ∂ν) * Z) := by
  let η := μ.restrict (closedExterior a R)
  obtain ⟨hkernel, hkernelBound⟩ := inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR
  have hdom₁ := (hφw.abs.mul_prod hkernel).const_mul ((2 : ℝ) ^ (m + 1))
  have hdom₂ := (hφ.abs.mul_prod hweighted).const_mul ((m + 1 : ℝ) * 2 ^ (m + 2) * H)
  have hm : Measurable (renormalizedNormalIntegrand m w φ a) := by
    unfold renormalizedNormalIntegrand inverseDistancePow
    fun_prop
  have hpoint : ∀ᵐ q ∂ν.prod η, |renormalizedNormalIntegrand m w φ a q| ≤
      2 ^ (m + 1) * (|φ q.1 * w q.1| * inverseDistancePow (m + 1) a q.2) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ q.1| * (|w q.2| * inverseDistancePow (m + 2) a q.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnear,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (closedExterior_measurable a R))] with q hx hy
    exact renormalizedNormalIntegrand_bound_of_support m w φ a q.1 q.2 H R hR hHR hx hy
  have hi : Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod η) := by
    apply (hdom₁.add hdom₂).mono' hm.aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using! hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q, 2 ^ (m + 1) * (|φ q.1 * w q.1| * inverseDistancePow (m + 1) a q.2) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          (|φ q.1| * (|w q.2| * inverseDistancePow (m + 2) a q.2)) ∂ν.prod η :=
      integral_mono_ae hi.abs (hdom₁.add hdom₂) hpoint
    _ = 2 ^ (m + 1) * ((∫ x, |φ x * w x| ∂ν) * (∫ y, inverseDistancePow (m + 1) a y ∂η)) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          ((∫ x, |φ x| ∂ν) * (∫ y, |w y| * inverseDistancePow (m + 2) a y ∂η)) := by
      rw [integral_add hdom₁ hdom₂]
      simp only [integral_const_mul]
      rw [integral_prod_mul (fun x => |φ x * w x|) (inverseDistancePow (m + 1) a),
        integral_prod_mul (fun x => |φ x|) (fun y => |w y| * inverseDistancePow (m + 2) a y)]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hkernelBound (integral_nonneg fun _ => abs_nonneg _)) (by positivity))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hZ (integral_nonneg fun _ => abs_nonneg _)) (by positivity))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalPairingEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal cutoff pairings and local energy

The normal pairing splits into a symmetric interaction inside a ball and a
renormalized exterior term. Bounds on the pairing, cutoff moments, and exterior
interaction control the local fractional energy together with its cutoff error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem normalCutoffPairing_energy_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (K L : ℝ≥0) (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hmass : C * R ^ (p + 1) ≤ M)
    (hsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (p + 1 + 2) a y)
      (closedExterior a R) μ)
    (Z : ℝ) (hZ : (∫ y in closedExterior a R, |w y| * inverseDistancePow (p + 1 + 2) a y ∂μ) ≤ Z)
    (A : ℝ) (hsmall : |normalCutoffPairing (p + 1) μ a R w χ| ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
        2 * (A + normalExteriorEstimate (p + 1) C M H R δ Z) +
          localCutoffErrorCoefficient p C L R * (M * δ ^ 2) := by
  let ν := μ.restrict (ball a R)
  let φ := fun x => χ x ^ 2 * w x
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hC := hg.1
  have hL2 := lipschitz_height_memLp_on_ball (p + 1) C μ hg w K hw a R hR
  have hmassν : ν.real univ ≤ M :=
    (ball_restriction_mass_bound (p + 1) C μ hg a R hR).trans hmass
  obtain ⟨hφ, hφw, hφ₁, hφ₂⟩ := squared_cutoff_test_moment_bounds ν w χ
    hw.continuous.measurable hχ.continuous.measurable hL2 hχbound M δ hM hδ hmassν hsecond
  have hφm : Measurable φ := (hχ.continuous.measurable.pow_const 2).mul hw.continuous.measurable
  have hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply hχsupport x
    intro hz
    exact hx (by simp only [φ, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul])
  obtain ⟨hExt, hExtBound⟩ := renormalized_far_pairing_integrable_and_bound (p + 1) C μ ν hg
    w φ hw.continuous.measurable hφm hφ hφw a H R hH hR hHR hnear hweighted Z hZ
  have hZ0 : 0 ≤ Z := (integral_nonneg fun y =>
    mul_nonneg (abs_nonneg (w y)) (inverseDistancePow_nonneg _ _ _)).trans hZ
  have hExtBound' : (∫ q, |renormalizedNormalIntegrand (p + 1) w φ a q|
      ∂ν.prod (μ.restrict (closedExterior a R))) ≤ normalExteriorEstimate (p + 1) C M H R δ Z := by
    apply hExtBound.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ₂ (by positivity)) (by positivity))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ₁ hZ0) (by positivity))
  have hExtAbs : |∫ q, renormalizedNormalIntegrand (p + 1) w φ a q
      ∂ν.prod (μ.restrict (closedExterior a R))| ≤ normalExteriorEstimate (p + 1) C M H R δ Z := by
    apply LE.le.trans _ hExtBound'
    simpa only [Real.norm_eq_abs] using! norm_integral_le_integral_norm
      (renormalizedNormalIntegrand (p + 1) w φ a)
  have hInner : (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) w φ q.1 q.2 ∂ν.prod ν) ≤
      2 * (A + normalExteriorEstimate (p + 1) C M H R δ Z) := by
    have hp := (le_abs_self (normalCutoffPairing (p + 1) μ a R w χ)).trans hsmall
    have hlow := (abs_le.mp hExtAbs).1
    change (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) w φ q.1 q.2 ∂ν.prod ν) +
      (∫ q, renormalizedNormalIntegrand (p + 1) w φ a q ∂ν.prod (μ.restrict (closedExterior a R))) ≤ A at hp
    linarith
  let W : ℝ≥0 := ⟨|w a| + (K : ℝ) * R, by positivity⟩
  have hLocal := localized_cutoff_energy_bound p C ν
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) (ball a R)
    (ae_restrict_mem measurableSet_ball) w χ hw.continuous.measurable hL2 K L W 1
    hw.lipschitzOnWith hχ (fun x hx => lipschitz_height_bound_on_ball w K hw a x R hx)
    (fun x _ => hχbound x) (2 * R) (by positivity) (ball_restriction_pair_diameter μ a R)
    (2 * (A + normalExteriorEstimate (p + 1) C M H R δ Z)) hInner
  refine ⟨hLocal.1, hLocal.2.trans ?_⟩
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecond (by positivity))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_UniformHeightTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem heightTailLinearCoefficient_nonneg (m : ℕ) (C B R b : ℝ) (K : ℝ≥0) (W : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 < R) (hb : b < 2) (hW : 0 ≤ W) :
    0 ≤ heightTailLinearCoefficient m C B R b K W := by
  have hden : 0 < 1 - b / 2 := by linarith
  unfold heightTailLinearCoefficient
  positivity

theorem weighted_height_tail_linear_bound {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (w : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (N : ℕ)
    (δ b W : ℝ) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hW : |w a| ≤ W) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hsecond : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * b ^ k) ^ 2) :
    IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y) (closedExterior a R) μ ∧
      (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) ≤
        heightTailLinearCoefficient m C B R b K W * δ := by
  obtain ⟨hi, hbound⟩ := improved_weighted_height_tail_bound m C B μ hg hCB w K hw a R hR N
    δ b hδ hb0 hb2 hsecond
  have hC := hg.1
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hW
  have hT : R ≤ R * (2 : ℝ) ^ N := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hR.le
  have hTpos : 0 < R * (2 : ℝ) ^ N := by positivity
  have hcenter : |w a| / (R * 2 ^ N) ≤ W / R :=
    (div_le_div_of_nonneg_right hW hTpos.le).trans
      (div_le_div_of_nonneg_left hW0 hR hT)
  have htail : 2 * (C * 2 ^ m / (R * 2 ^ N)) ≤ (2 * (C * 2 ^ m)) * δ := by
    simpa only [div_eq_mul_inv, mul_assoc] using!
      mul_le_mul_of_nonneg_left hlast (show 0 ≤ 2 * (C * 2 ^ m) by positivity)
  refine ⟨hi, hbound.trans ?_⟩
  calc
    _ ≤ (B * δ / R) / (1 - b / 2) +
        ((K : ℝ) + W / R) * ((2 * (C * 2 ^ m)) * δ) :=
      add_le_add le_rfl (mul_le_mul (add_le_add le_rfl hcenter) htail (by positivity) (by positivity))
    _ = _ := by unfold heightTailLinearCoefficient; ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalizedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem fractionalPairEnergy_div {X : Type*} [MetricSpace X]
    (m : ℕ) (f : X → ℝ) (δ : ℝ) (x y : X) :
    fractionalPairEnergy m (fun z => f z / δ) x y = fractionalPairEnergy m f x y / δ ^ 2 := by
  unfold fractionalPairEnergy
  rw [← sub_div, div_pow]
  ring

theorem normalizedEnergyCoefficient_nonneg (p : ℕ) (C M H R A J : ℝ) (L : ℝ≥0)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hH : 0 ≤ H) (hR : 0 < R) (hA : 0 ≤ A) (hJ : 0 ≤ J) :
    0 ≤ normalizedEnergyCoefficient p C M H R A J L := by
  unfold normalizedEnergyCoefficient localCutoffErrorCoefficient
  positivity

theorem normalized_cutoff_energy_bound {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (w χ : Ambient d → ℝ) (K L : ℝ≥0) (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M δ b W A : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hW : |w a| ≤ W) (hA : 0 ≤ A) (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * b ^ k) ^ 2)
    (hsmall : |normalCutoffPairing (p + 1) μ a R w χ| ≤ A * δ ^ 2) :
    0 ≤ normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2)
        ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
        normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L := by
  let J := heightTailLinearCoefficient (p + 1) C B R b K W
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hJ : 0 ≤ J := heightTailLinearCoefficient_nonneg (p + 1) C B R b K W
    hg.1 hB hR hb2 ((abs_nonneg _).trans hW)
  obtain ⟨hweighted, hZ⟩ := weighted_height_tail_linear_bound (p + 1) C B μ hg hCB w K hw
    a R hR N δ b W hδ.le hb0 hb2 hW hlast hshell
  obtain ⟨hE, hEnergyBound⟩ := normalCutoffPairing_energy_bound p C μ hg w χ K L hw hχ hχbound
    a H R hH hR hHR hχsupport M δ hM hδ.le hmass hsecond hweighted (J * δ) hZ (A * δ ^ 2) hsmall
  have hUnscaled : (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
      normalizedEnergyCoefficient p C M H R A J L * δ ^ 2 := by
    convert! hEnergyBound using 1
    all_goals try with_reducible_and_instances rfl
    unfold normalExteriorEstimate normalizedEnergyCoefficient
    push_cast
    ring
  refine ⟨normalizedEnergyCoefficient_nonneg p C M H R A J L hg.1 hM hH hR hA hJ, ?_, ?_⟩
  · simpa only [fractionalPairEnergy_div] using! hE.div_const (δ ^ 2)
  · simp_rw [fractionalPairEnergy_div]
    rw [integral_div]
    exact (div_le_iff₀ (sq_pos_of_pos hδ)).mpr hUnscaled

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NormalizedLocalEnergyBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local integrability of normalized Lipschitz energies

Growth bounds make normalized Lipschitz functions square-integrable on balls and
their fractional pair energies integrable on the corresponding product measure.
An auxiliary sequence bound absorbs finitely many exceptional scales into one nonnegative bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem normalized_lipschitz_memLp_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (r δ : ℝ) (hr : 0 < r) :
    MemLp (fun x => u x / δ) 2 (μ.restrict (ball a r)) := by
  have h := (lipschitz_height_memLp_on_ball n G μ hg u K hu a r hr).const_smul δ⁻¹
  change MemLp (fun x => δ⁻¹ * u x) 2 (μ.restrict (ball a r)) at h
  simpa only [div_eq_mul_inv, mul_comm] using! h

theorem normalized_lipschitz_energy_integrable_on_ball {d : ℕ} (p : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth (p + 1) G μ)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (r δ : ℝ) (hr : 0 < r) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2)
      ((μ.restrict (ball a r)).prod (μ.restrict (ball a r))) := by
  let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) G μ hg a r hr
  have hK : ∀ᵐ q ∂(μ.restrict (ball a r)).prod (μ.restrict (ball a r)),
      |u q.1 - u q.2| ≤ (K : ℝ) * dist q.1 q.2 := by
    exact Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hu.dist_le_mul q.1 q.2
  have hE := fractionalEnergy_integrable_of_ae_lipschitz p G (μ.restrict (ball a r))
    (globalGrowth_restrict (p + 1) G μ hg (ball a r)) u hu.continuous.measurable K hK
    (2 * r) (by positivity) (ball_restriction_pair_diameter μ a r)
  simpa only [fractionalPairEnergy_div] using! hE.div_const (δ ^ 2)

theorem nonnegative_uniform_bound_of_eventually_le (f : ℕ → ℝ) (B : ℝ)
    (hB : ∀ᶠ j in atTop, f j ≤ B) : ∃ M : ℝ, 0 ≤ M ∧ ∀ j, f j ≤ M := by
  have h : IsBoundedUnder (· ≤ ·) atTop f := ⟨B, hB⟩
  obtain ⟨M, hM⟩ := h.bddAbove_range
  exact ⟨max 0 M, le_max_left _ _, fun j => (hM ⟨j, rfl⟩).trans (le_max_right _ _)⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicSourceTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem dyadic_shifted_last_error_identity (q N : ℕ) (hN : q + 1 ≤ N) (δ : ℝ) :
    ((2 : ℝ) ^ q * 2 ^ (N - (q + 1)))⁻¹ / δ = 2 * (((2 : ℝ) ^ N)⁻¹ / δ) := by
  have hp : (2 : ℝ) ^ (q + 1) * 2 ^ (N - (q + 1)) = (2 : ℝ) ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hN]
  rw [pow_succ] at hp
  have hr : (2 : ℝ) ^ q * 2 ^ (N - (q + 1)) = (2 : ℝ) ^ N / 2 := by nlinarith [hp]
  rw [hr, inv_div]
  ring

theorem dyadic_shifted_last_error_tendsto (q : ℕ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (hN : Tendsto N atTop atTop)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0)) :
    Tendsto (fun j => N j - (q + 1)) atTop atTop ∧
      Tendsto (fun j => ((2 : ℝ) ^ q * 2 ^ (N j - (q + 1)))⁻¹ / δ j) atTop (𝓝 0) := by
  refine ⟨(tendsto_sub_atTop_nat (q + 1)).comp hN, ?_⟩
  have h := hlast.const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop (q + 1))] with j hj
  exact (dyadic_shifted_last_error_identity q (N j) hj (δ j)).symm

theorem dyadic_ball_to_shell_moment_identity (m q k : ℕ) (D δ b : ℝ) :
    δ ^ 2 * D * ((2 : ℝ) ^ (q + k + 1)) ^ m *
        ((2 : ℝ) ^ (q + k + 1) * b ^ (q + k + 1)) ^ 2 =
      ((D * (2 : ℝ) ^ (m + 2) * (b ^ (q + 1)) ^ 2) * ((2 : ℝ) ^ q * 2 ^ k) ^ m) *
        (δ * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 := by
  simp only [pow_add, pow_succ, mul_pow]
  ring

theorem controlled_shell_moments_from_dyadic_balls {d : ℕ} (m : ℕ)
    (μ : ℕ → Measure (Ambient d)) (a : Ambient d) (u : ℕ → Ambient d → ℝ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) (D b Bmin : ℝ)
    (hw : ∀ l j, MemLp (u j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))))
    (hbound : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ m * ((2 : ℝ) ^ l * b ^ l) ^ 2) (q : ℕ) :
    ∃ B : ℝ, Bmin ≤ B ∧ ∀ j k, k < N j - (q + 1) →
      (∫ x in dyadicAnnulus a ((2 : ℝ) ^ q) k, u j x ^ 2 ∂μ j) ≤
        (B * ((2 : ℝ) ^ q * 2 ^ k) ^ m) * (δ j * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 := by
  let B₀ := D * (2 : ℝ) ^ (m + 2) * (b ^ (q + 1)) ^ 2
  refine ⟨max Bmin B₀, le_max_left _ _, ?_⟩
  intro j k hk
  have hcontrol : q + k + 1 ≤ N j := by omega
  have hsub : dyadicAnnulus a ((2 : ℝ) ^ q) k ⊆ ball a ((2 : ℝ) ^ (q + k + 1)) := by
    convert! dyadicAnnulus_subset_ball a ((2 : ℝ) ^ q) k using 1
    all_goals try with_reducible_and_instances rfl
    rw [← pow_add]
    congr 2
  calc
    _ ≤ ∫ x in ball a ((2 : ℝ) ^ (q + k + 1)), u j x ^ 2 ∂μ j :=
      integral_mono_measure (Measure.restrict_mono hsub le_rfl)
        (Eventually.of_forall (fun x => sq_nonneg (u j x))) (hw (q + k + 1) j).integrable_sq
    _ ≤ δ j ^ 2 * D * ((2 : ℝ) ^ (q + k + 1)) ^ m *
        ((2 : ℝ) ^ (q + k + 1) * b ^ (q + k + 1)) ^ 2 := hbound j (q + k + 1) hcontrol
    _ = (B₀ * ((2 : ℝ) ^ q * 2 ^ k) ^ m) *
        (δ j * ((2 : ℝ) ^ q * 2 ^ k) * b ^ k) ^ 2 :=
      dyadic_ball_to_shell_moment_identity m q k D (δ j) b
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Bmin B₀) (by positivity)) (sq_nonneg _)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_RieszPairingIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar Riesz pairings and affine normal heights

Pairing the Riesz kernel with a fixed normal identifies its interior contribution
with the fractional bilinear form. For mean-zero tests, the exterior correction
integrates to zero, identifying the scalar Riesz pairing with the normal cutoff pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem affineNormalHeight_difference {d : ℕ} (e z : Ambient d) (b : ℝ) (x y : Ambient d) :
    affineNormalHeight e z b x - affineNormalHeight e z b y = inner ℝ e (x - y) := by
  rw [affineNormalHeight, affineNormalHeight, centered_coordinate_difference]
  exact normal_coordinate_difference e z x y

theorem affineNormalHeight_lipschitz {d : ℕ} (e z : Ambient d) (b : ℝ) :
    LipschitzWith ‖e‖₊ (affineNormalHeight e z b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, affineNormalHeight_difference]
  simpa only [Real.norm_eq_abs, coe_nnnorm, dist_eq_norm] using!
    norm_inner_le_norm (𝕜 := ℝ) e (x - y)

theorem kernel_inner_normal_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (w : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y)) (x y : Ambient d) :
    inner ℝ e (kernel m x y) = (w x - w y) * inverseDistancePow (m + 1) x y := by
  rw [kernel, real_inner_smul_right, ← hw x y, ← dist_eq_norm]
  unfold inverseDistancePow
  ring

theorem rieszInteriorIntegrand_eq_fractionalBilinear {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q = fractionalBilinear m w φ q.1 q.2 := by
  rw [rieszInteriorIntegrand, kernel_inner_normal_difference m e w hw]
  unfold inverseDistancePow fractionalBilinear
  ring

theorem rieszFarIntegrand_eq_normal_sub_correction {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (q : Ambient d × Ambient d) :
    rieszFarIntegrand m e φ a q = renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
  rw [rieszFarIntegrand, inner_sub_right, kernel_inner_normal_difference m e w hw,
    kernel_inner_normal_difference m e w hw]
  unfold renormalizedNormalIntegrand
  ring

theorem riesz_far_integral_eq_normal {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (e : Ambient d) (w φ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod (μ.restrict (closedExterior a R)))) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod (μ.restrict (closedExterior a R))) ∧
      (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod (μ.restrict (closedExterior a R))) =
        ∫ q, renormalizedNormalIntegrand m w φ a q ∂ν.prod (μ.restrict (closedExterior a R)) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR).1
  have hcorrection := (hφ.mul_const (w a)).mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q => renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
    funext q
    exact rieszFarIntegrand_eq_normal_sub_correction m e w φ hw a q
  rw [heq]
  refine ⟨hN.sub hcorrection, ?_⟩
  rw [integral_sub hN hcorrection, integral_prod_mul (fun x => φ x * w a) (inverseDistancePow (m + 1) a),
    integral_mul_const, hzero, zero_mul, zero_mul, sub_zero]

theorem normalCutoffPairing_eq_rieszScalarPairing {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (w χ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hφ : Integrable (fun x => χ x ^ 2 * w x) (μ.restrict (ball a R)))
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w (fun x => χ x ^ 2 * w x) a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    normalCutoffPairing m μ a R w χ = rieszScalarPairing m μ a R e (fun x => χ x ^ 2 * w x) := by
  have := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hext := (riesz_far_integral_eq_normal m C μ (μ.restrict (ball a R)) hg e w
    (fun x => χ x ^ 2 * w x) hw a R hR hφ hzero hN).2
  unfold normalCutoffPairing rieszScalarPairing
  simp_rw [rieszInteriorIntegrand_eq_fractionalBilinear m e w _ hw]
  rw [hext]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_VectorNormalizedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normal cutoff pairing is identified with a Riesz scalar pairing for a centered
Lipschitz height test, using local `L²` integrability and cutoff support control.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem normalCutoffPairing_eq_riesz_of_lipschitz {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (w χ : Ambient d → ℝ) (K : ℝ≥0) (hw : LipschitzWith K w)
    (hcoord : ∀ x y, w x - w y = inner ℝ e (x - y))
    (hχm : Measurable χ) (hχbound : ∀ x, |χ x| ≤ 1)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0) :
    normalCutoffPairing m μ a R w χ =
      rieszScalarPairing m μ a R e (fun x => χ x ^ 2 * w x) := by
  let ν := μ.restrict (ball a R)
  let φ := fun x => χ x ^ 2 * w x
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w K hw a R hR
  have hφL2 := squared_cutoff_test_memLp ν w χ hw.continuous.measurable hχm hwL2 hχbound
  have hφ : Integrable φ ν := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν :=
    memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hwL2))
  have hφm : Measurable φ := (hχm.pow_const 2).mul hw.continuous.measurable
  have hnear : ∀ᵐ x ∂ν, φ x ≠ 0 → dist x a ≤ H := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply hχsupport x
    intro hz
    exact hx (by simp only [φ, hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul])
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w K hw a R hR
  have hN := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφm hφ hφw a H R hH hR hHR hnear hweighted _ hZ).1
  exact normalCutoffPairing_eq_rieszScalarPairing m C μ hg e w χ hcoord a R hR hφ hzero hN

theorem normalized_energy_from_vector_pairing {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (e : Ambient d) (w χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hcoord : ∀ x y, w x - w y = inner ℝ e (x - y))
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (H R : ℝ)
    (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M δ b W A : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hW : |w a| ≤ W) (hA : 0 ≤ A) (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * b ^ k) ^ 2)
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0)
    (hsmall : |rieszScalarPairing (p + 1) μ a R e (fun x => χ x ^ 2 * w x)| ≤ A * δ ^ 2) :
    0 ≤ normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2)
        ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => (χ x * w x) / δ) q.1 q.2
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) ≤
        normalizedEnergyCoefficient p C M H R A (heightTailLinearCoefficient (p + 1) C B R b K W) L := by
  have heq := normalCutoffPairing_eq_riesz_of_lipschitz (p + 1) C μ hg e w χ K hw hcoord
    hχ.continuous.measurable hχbound a H R hH hR hHR hχsupport hzero
  rw [← heq] at hsmall
  exact normalized_cutoff_energy_bound p C B μ hg hCB w χ K L hw hχ hχbound
    a H R hH hR hHR hχsupport M δ b W A hM hδ hb0 hb2 hW hA N hlast hmass hsecond hshell hsmall

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_WeightedCentering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

theorem cutoffMean_integral_zero (ν : Measure X) [IsFiniteMeasure ν]
    (u χ : X → ℝ) (hu : Measurable u) (hχ : Measurable χ)
    (huL2 : MemLp u 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (hdenom : (∫ x, χ x ^ 2 ∂ν) ≠ 0) :
    (∫ x, χ x ^ 2 * (u x - cutoffMean ν u χ) ∂ν) = 0 := by
  have htest := (squared_cutoff_test_memLp ν u χ hu hχ huL2 hbound).integrable (by norm_num)
  have hχL2 : MemLp χ 2 ν := MemLp.of_bound hχ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  simp_rw [mul_sub]
  rw [integral_sub htest (hχL2.integrable_sq.mul_const _), integral_mul_const]
  unfold cutoffMean
  field_simp
  ring

theorem cutoffMean_sq_bound (ν : Measure X) [IsFiniteMeasure ν]
    (u χ : X → ℝ) (hu : Measurable u) (hχ : Measurable χ)
    (huL2 : MemLp u 2 ν) (hbound : ∀ x, |χ x| ≤ 1)
    (c : ℝ) (hc : 0 < c) (hmass : c ≤ ∫ x, χ x ^ 2 ∂ν) :
    cutoffMean ν u χ ^ 2 ≤ (∫ x, u x ^ 2 ∂ν) / c := by
  have hχL2 : MemLp χ 2 ν := MemLp.of_bound hχ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  have hχuL2 := bounded_multiplier_memLp ν u χ hu hχ huL2 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  have he : (∫ x, (χ x * u x) ^ 2 ∂ν) ≤ ∫ x, u x ^ 2 ∂ν := by
    apply integral_mono hχuL2.integrable_sq huL2.integrable_sq
    intro x
    change (χ x * u x) ^ 2 ≤ u x ^ 2
    rw [mul_pow]
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right (cutoff_square_le_one χ hbound x) (sq_nonneg (u x))
  have hcs := integral_mul_cauchy_schwarz_sq ν (fun x => χ x * u x) χ hχuL2 hχL2
  have hpoint : (fun x => (χ x * u x) * χ x) = fun x => χ x ^ 2 * u x := by
    funext x
    ring
  rw [hpoint] at hcs
  have hd : 0 < ∫ x, χ x ^ 2 ∂ν := hc.trans_le hmass
  have hnum : (∫ x, χ x ^ 2 * u x ∂ν) ^ 2 ≤
      (∫ x, u x ^ 2 ∂ν) * (∫ x, χ x ^ 2 ∂ν) :=
    hcs.trans (mul_le_mul_of_nonneg_right he hd.le)
  calc
    cutoffMean ν u χ ^ 2 ≤ (∫ x, u x ^ 2 ∂ν) / (∫ x, χ x ^ 2 ∂ν) := by
      unfold cutoffMean
      rw [div_pow]
      apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
      convert! hnum using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (integral_nonneg fun x => sq_nonneg (u x)) hc hmass

theorem centered_second_moment_le (ν : Measure X) [IsFiniteMeasure ν]
    (u : X → ℝ) (huL2 : MemLp u 2 ν) (b : ℝ) :
    (∫ x, (u x - b) ^ 2 ∂ν) ≤ 2 * (∫ x, u x ^ 2 ∂ν) + 2 * ν.real univ * b ^ 2 := by
  calc
    _ ≤ ∫ x, 2 * u x ^ 2 + 2 * b ^ 2 ∂ν := by
      apply integral_mono ((huL2.sub (memLp_const b)).integrable_sq)
        ((huL2.integrable_sq.const_mul 2).add (integrable_const _))
      intro x
      change (u x - b) ^ 2 ≤ 2 * u x ^ 2 + 2 * b ^ 2
      nlinarith [sq_nonneg (u x + b)]
    _ = _ := by
      rw [integral_add (huL2.integrable_sq.const_mul 2) (integrable_const _),
        integral_const_mul, integral_const]
      simp only [smul_eq_mul]
      ring

theorem cutoff_mass_lower_of_one_on (ν : Measure X) [IsFiniteMeasure ν]
    (χ : X → ℝ) (hχ : Measurable χ) (hbound : ∀ x, |χ x| ≤ 1)
    (s : Set X) (hs : MeasurableSet s) (hone : ∀ x ∈ s, χ x = 1) :
    ν.real s ≤ ∫ x, χ x ^ 2 ∂ν := by
  have hχL2 : MemLp χ 2 ν := MemLp.of_bound hχ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hbound x)
  calc
    ν.real s = ∫ x in s, χ x ^ 2 ∂ν := by
      calc
        ν.real s = ∫ _ in s, (1 : ℝ) ∂ν := by simp
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hs] with x hx
          rw [hone x hx, one_pow]
    _ ≤ _ := setIntegral_le_integral hχL2.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (χ x))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_InnerEnergyRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem inner_fractional_energy_le_cutoff {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ]
    (s t : Set (Ambient d)) (hs : MeasurableSet s) (hst : s ⊆ t)
    (u χ : Ambient d → ℝ) (b δ : ℝ) (hone : ∀ x ∈ s, χ x = 1)
    (hE : Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy m (fun x => χ x * (u x - b) / δ) q.1 q.2)
      ((μ.restrict t).prod (μ.restrict t))) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy m (fun x => u x / δ) q.1 q.2)
      ((μ.restrict s).prod (μ.restrict s)) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy m (fun x => u x / δ) q.1 q.2
          ∂(μ.restrict s).prod (μ.restrict s)) ≤
      ∫ q : Ambient d × Ambient d,
        fractionalPairEnergy m (fun x => χ x * (u x - b) / δ) q.1 q.2
          ∂(μ.restrict t).prod (μ.restrict t) := by
  have hmeasure : (μ.restrict s).prod (μ.restrict s) ≤ (μ.restrict t).prod (μ.restrict t) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (Set.prod_mono hst hst) le_rfl
  have heq : (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy m (fun x => u x / δ) q.1 q.2) =ᵐ[(μ.restrict s).prod (μ.restrict s)]
      (fun q => fractionalPairEnergy m (fun x => χ x * (u x - b) / δ) q.1 q.2) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs)] with q hx hy
    unfold fractionalPairEnergy
    dsimp only
    rw [hone q.1 hx, hone q.2 hy, one_mul, one_mul]
    congr 2
    ring
  refine ⟨(integrable_congr heq).mpr (hE.mono_measure hmeasure), ?_⟩
  rw [integral_congr_ae heq]
  exact integral_mono_measure hmeasure
    (Filter.Eventually.of_forall fun q => fractionalPairEnergy_nonneg m _ q.1 q.2) hE

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_CenteredShellMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Second-moment and mass bounds control moments after subtracting a constant. Applying this
estimate to dyadic annuli yields centered shell bounds at the prescribed geometric scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem centered_moment_from_scale {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (u : X → ℝ) (hu : MemLp u 2 ν)
    (M D δ A b : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hmass : ν.real univ ≤ M) (hsecond : (∫ x, u x ^ 2 ∂ν) ≤ M * A ^ 2)
    (hb : b ^ 2 ≤ D * δ ^ 2) (hscale : δ ^ 2 ≤ A ^ 2) :
    (∫ x, (u x - b) ^ 2 ∂ν) ≤ (2 * (1 + D) * M) * A ^ 2 := by
  have hbA := hb.trans (mul_le_mul_of_nonneg_left hscale hD)
  apply (centered_second_moment_le ν u hu b).trans
  calc
    _ ≤ 2 * (M * A ^ 2) + 2 * M * (D * A ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hsecond (by norm_num))
        (mul_le_mul (mul_le_mul_of_nonneg_left hmass (by norm_num)) hbA (sq_nonneg _) (by positivity))
    _ = _ := by ring

theorem centered_shell_second_moment {d : ℕ} (m : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth m C μ) (hCB : C * 2 ^ m ≤ B)
    (u : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (R : ℝ) (hR : 1 ≤ R) (k : ℕ)
    (δ β D b : ℝ) (hδ : 0 ≤ δ) (hβ : 1 ≤ β) (hD : 0 ≤ D)
    (hb : b ^ 2 ≤ D * δ ^ 2)
    (hsecond : (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * β ^ k) ^ 2) :
    (∫ y in dyadicAnnulus a R k, (u y - b) ^ 2 ∂μ) ≤
      ((2 * (1 + D) * B) * (R * 2 ^ k) ^ m) * (δ * (R * 2 ^ k) * β ^ k) ^ 2 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let ν := μ.restrict (dyadicAnnulus a R k)
  have : IsFiniteMeasure ν := ⟨by
    simpa only [ν, Measure.restrict_apply_univ] using! dyadicAnnulus_measure_lt_top m C μ hg a R hRpos k⟩
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hmass : ν.real univ ≤ B * (R * 2 ^ k) ^ m := by
    have hmass' : μ.real (dyadicAnnulus a R k) ≤ C * (R * 2 ^ (k + 1)) ^ m :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (by positivity))
        ((measure_mono (dyadicAnnulus_subset_ball a R k)).trans (hg.2 a _ (by positivity)))
    have heq : C * (R * (2 : ℝ) ^ (k + 1)) ^ m = (C * 2 ^ m) * (R * 2 ^ k) ^ m := by
      rw [pow_succ, show R * ((2 : ℝ) ^ k * 2) = (R * 2 ^ k) * 2 by ring, mul_pow]
      ring
    simpa only [ν, Measure.real, Measure.restrict_apply_univ] using!
      hmass'.trans (heq ▸ mul_le_mul_of_nonneg_right hCB (by positivity))
  have hscale : δ ≤ δ * (R * 2 ^ k) * β ^ k := by
    have ht : 1 ≤ R * (2 : ℝ) ^ k := hR.trans (by
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hRpos.le)
    calc
      δ ≤ δ * (R * 2 ^ k) := by simpa only [mul_one] using! mul_le_mul_of_nonneg_left ht hδ
      _ ≤ _ := by simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (one_le_pow₀ hβ) (by positivity : 0 ≤ δ * (R * 2 ^ k))
  have h := centered_moment_from_scale ν u (lipschitz_height_memLp_on_annulus m C μ hg u K hu a R hRpos k)
    (B * (R * 2 ^ k) ^ m) D δ (δ * (R * 2 ^ k) * β ^ k) b (by positivity) hD hmass hsecond hb
    (pow_le_pow_left₀ hδ hscale 2)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem cutoffMean_sq_le_amplitude {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (u χ : X → ℝ)
    (hu : Measurable u) (hχ : Measurable χ) (huL2 : MemLp u 2 ν)
    (hχbound : ∀ x, |χ x| ≤ 1) (c M δ : ℝ) (hc : 0 < c)
    (hcutmass : c ≤ ∫ x, χ x ^ 2 ∂ν)
    (hsecond : (∫ x, u x ^ 2 ∂ν) ≤ M * δ ^ 2) :
    cutoffMean ν u χ ^ 2 ≤ (M / c) * δ ^ 2 := by
  apply (cutoffMean_sq_bound ν u χ hu hχ huL2 hχbound c hc hcutmass).trans
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using!
    div_le_div_of_nonneg_right hsecond hc.le

theorem cutoffMean_abs_le_uniform {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (u χ : X → ℝ)
    (hu : Measurable u) (hχ : Measurable χ) (huL2 : MemLp u 2 ν)
    (hχbound : ∀ x, |χ x| ≤ 1) (c M δ : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hcutmass : c ≤ ∫ x, χ x ^ 2 ∂ν)
    (hsecond : (∫ x, u x ^ 2 ∂ν) ≤ M * δ ^ 2) :
    |cutoffMean ν u χ| ≤ Real.sqrt (M / c) := by
  have hs := cutoffMean_sq_le_amplitude ν u χ hu hχ huL2 hχbound c M δ hc hcutmass hsecond
  have hδsq : δ ^ 2 ≤ 1 := by nlinarith
  have hsq : cutoffMean ν u χ ^ 2 ≤ M / c :=
    hs.trans (by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hδsq (by positivity : 0 ≤ M / c))
  have hr := Real.sq_sqrt (show 0 ≤ M / c by positivity)
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by simpa only [sq_abs, hr] using! hsq)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_UncenteredEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Subtracting the cutoff mean reduces an uncentered height test to the normalized energy
estimate. Centered moment and tail bounds determine the resulting quantitative coefficient.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem uncentered_inner_energy_bound {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (e : Ambient d) (u χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hu : LipschitzWith K u) (hχ : LipschitzWith L χ)
    (hcoord : ∀ x y, u x - u y = inner ℝ e (x - y))
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (r H R : ℝ)
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hHR : 2 * H ≤ R) (hrR : r ≤ R)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hχone : ∀ x ∈ ball a r, χ x = 1)
    (M c δ β W A : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ1 : 1 ≤ β) (hβ2 : β < 2) (hW : |u a| ≤ W) (hA : 0 ≤ A)
    (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hcutmass : c ≤ ∫ x in ball a R, χ x ^ 2 ∂μ)
    (hsecond : (∫ x in ball a R, u x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * β ^ k) ^ 2)
    (hsmall : |rieszScalarPairing (p + 1) μ a R e
      (fun x => χ x ^ 2 * (u x - cutoffMean (μ.restrict (ball a R)) u χ))| ≤ A * δ ^ 3) :
    0 ≤ uncenteredEnergyCoefficient p C B M c H R β W A K L ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2)
        ((μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2
          ∂(μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ≤
        uncenteredEnergyCoefficient p C B M c H R β W A K L := by
  let ν := μ.restrict (ball a R)
  let b := cutoffMean ν u χ
  let w := fun x => u x - b
  let D := M / c
  let F := 2 * (1 + D)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hD : 0 ≤ D := div_nonneg hM hc.le
  have hF : 1 ≤ F := by dsimp [F] <;> linarith
  have hB : 0 ≤ B := (mul_nonneg hg.1 (by positivity)).trans hCB
  have hCB' : C * 2 ^ (p + 1) ≤ F * B := hCB.trans
    (by simpa only [one_mul] using! mul_le_mul_of_nonneg_right hF hB)
  have hM' : M ≤ F * M := by simpa only [one_mul] using! mul_le_mul_of_nonneg_right hF hM
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hRpos
  have huL2 := lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a R hRpos
  have hνmass : ν.real univ ≤ M :=
    (ball_restriction_mass_bound (p + 1) C μ hg a R hRpos).trans hmass
  have hb : b ^ 2 ≤ D * δ ^ 2 := cutoffMean_sq_le_amplitude ν u χ
    hu.continuous.measurable hχ.continuous.measurable huL2 hχbound c M δ hc hcutmass hsecond
  have hbabs : |b| ≤ Real.sqrt D := cutoffMean_abs_le_uniform ν u χ
    hu.continuous.measurable hχ.continuous.measurable huL2 hχbound c M δ hc hM hδ.le hδ1 hcutmass hsecond
  have hw : LipschitzWith K w := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [w, Real.dist_eq, centered_coordinate_difference] using! hu.dist_le_mul x y
  have hwcoord : ∀ x y, w x - w y = inner ℝ e (x - y) := by
    intro x y
    dsimp only [w]
    rw [centered_coordinate_difference, hcoord]
  have hwW : |w a| ≤ W + Real.sqrt D := by
    calc
      _ ≤ |u a| + |b| := by simpa only [w, sub_zero, zero_sub, abs_neg] using! abs_sub_le (u a) 0 b
      _ ≤ _ := add_le_add hW hbabs
  have hwsecond : (∫ x in ball a R, w x ^ 2 ∂μ) ≤ (F * M) * δ ^ 2 :=
    centered_moment_from_scale ν u huL2 M D δ δ b hM hD hνmass hsecond hb le_rfl
  have hwshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, w y ^ 2 ∂μ) ≤
      ((F * B) * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * β ^ k) ^ 2 := by
    intro k hk
    exact centered_shell_second_moment (p + 1) C B μ hg hCB u K hu a R hR k
      δ β D b hδ.le hβ1 hD hb (hshell k hk)
  have hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0 :=
    cutoffMean_integral_zero ν u χ hu.continuous.measurable hχ.continuous.measurable
      huL2 hχbound (ne_of_gt (hc.trans_le hcutmass))
  have hwsmall : |rieszScalarPairing (p + 1) μ a R e (fun x => χ x ^ 2 * w x)| ≤ A * δ ^ 2 := by
    apply hsmall.trans
    calc
      A * δ ^ 3 = (A * δ ^ 2) * δ := by ring
      _ ≤ (A * δ ^ 2) * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = _ := mul_one _
  obtain ⟨hconstant, hE, hbound⟩ := normalized_energy_from_vector_pairing p C (F * B) μ hg hCB'
    e w χ K L hw hχ hwcoord hχbound a H R hH hRpos hHR hχsupport
    (F * M) δ β (W + Real.sqrt D) A (mul_nonneg (by linarith) hM) hδ (by linarith) hβ2
    hwW hA N hlast (hmass.trans hM') hwsecond hwshell hzero hwsmall
  obtain ⟨hInner, hInnerBound⟩ := inner_fractional_energy_le_cutoff (p + 1) μ
    (ball a r) (ball a R) measurableSet_ball (ball_subset_ball hrR) u χ b δ hχone hE
  exact ⟨hconstant, hInner, hInnerBound.trans hbound⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalizedNormalTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem lipschitz_product_of_bound_on_support {X : Type*} [PseudoMetricSpace X]
    (f g : X → ℝ) (Kf Kg Bf Bg : ℝ≥0) (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hBf : ∀ x, |f x| ≤ (Bf : ℝ)) (hBg : ∀ x, f x ≠ 0 → |g x| ≤ (Bg : ℝ)) :
    LipschitzWith (Bf * Kg + Kf * Bg) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hf' : |f x - f y| ≤ (Kf : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hf.dist_le_mul x y
  have hg' : |g x - g y| ≤ (Kg : ℝ) * dist x y := by simpa only [Real.dist_eq] using! hg.dist_le_mul x y
  by_cases hy : f y = 0
  · by_cases hx : f x = 0
    · simp only [hx, hy, zero_mul, dist_self]
      positivity
    · calc
        dist (f x * g x) (f y * g y) = |f x - f y| * |g x| := by
          simp only [hy, zero_mul, Real.dist_eq, sub_zero, abs_mul]
        _ ≤ ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
          mul_le_mul hf' (hBg x hx) (abs_nonneg _) (by positivity)
        _ ≤ ((Bf * Kg + Kf * Bg : ℝ≥0) : ℝ) * dist x y := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          nlinarith [mul_nonneg (mul_nonneg Bf.coe_nonneg Kg.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · calc
      dist (f x * g x) (f y * g y) = |f x * (g x - g y) + (f x - f y) * g y| := by
        rw [Real.dist_eq]
        congr 1
        ring
      _ ≤ |f x| * |g x - g y| + |f x - f y| * |g y| := by
        simpa only [abs_mul] using! abs_add_le (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ (Bf : ℝ) * ((Kg : ℝ) * dist x y) + ((Kf : ℝ) * dist x y) * (Bg : ℝ) :=
        add_le_add (mul_le_mul (hBf x) hg' (abs_nonneg _) (by positivity))
          (mul_le_mul hf' (hBg y hy) (abs_nonneg _) (by positivity))
      _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul] <;> ring

theorem squared_cutoff_height_globally_lipschitz {X : Type*} [PseudoMetricSpace X]
    (w χ : X → ℝ) (K L W : ℝ≥0) (hw : LipschitzWith K w) (hχ : LipschitzWith L χ)
    (hbound : ∀ x, |χ x| ≤ 1) (hW : ∀ x, χ x ≠ 0 → |w x| ≤ (W : ℝ)) :
    LipschitzWith (K + 2 * L * W) (fun x => χ x ^ 2 * w x) := by
  have hsquare : LipschitzWith (1 * L + L * 1) (fun x => χ x ^ 2) := by
    simpa only [pow_two] using! lipschitz_bounded_product_real (Bf := 1) (Bg := 1) hχ hχ hbound hbound
  have h := lipschitz_product_of_bound_on_support (fun x => χ x ^ 2) w (1 * L + L * 1) K 1 W
    hsquare hw
    (fun x => by
      rw [abs_of_nonneg (sq_nonneg (χ x))]
      exact cutoff_square_le_one χ hbound x)
    (fun x hx => hW x (fun hz => hx (by simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)])))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem squared_cutoff_mean_zero_global {d : ℕ}
    (μ : Measure (Ambient d)) (w χ : Ambient d → ℝ) (a : Ambient d) (H R : ℝ)
    (hHR : H < R) (hsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0) :
    (∫ x, χ x ^ 2 * w x ∂μ) = 0 := by
  have heq : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = ∫ x, χ x ^ 2 * w x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : χ x = 0 := by
      by_contra hn
      exact hx ((hsupport x hn).trans_lt hHR)
    simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  exact heq.symm.trans hzero

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_FiniteRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-measure truncated Riesz pairings

The scalar truncated kernel is measurable and bounded away from its singularity.
Symmetrization expresses finite-measure pairings as interior double integrals,
whose integrability yields convergence as the truncation scale tends to zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszInteriorIntegrand_integrable_of_lipschitz {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    Integrable (rieszInteriorIntegrand (p + 1) e φ) (ν.prod ν) := by
  let w := affineNormalHeight e 0 0
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e 0 0
  have hI := fractionalBilinear_integrable_of_ae_lipschitz p C ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable ‖e‖₊ L
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hw.dist_le_mul q.1 q.2)
    (Filter.Eventually.of_forall fun q => by simpa only [Real.dist_eq] using! hφ.dist_le_mul q.1 q.2)
    r hr hdiam
  have heq : rieszInteriorIntegrand (p + 1) e φ =
      fun q => fractionalBilinear (p + 1) w φ q.1 q.2 := by
    funext q
    exact rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e w φ
      (affineNormalHeight_difference e 0 0) q
  rw [heq]
  exact hI

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SymmetricPairingSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set

theorem integral_symmetric_pair_split {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (s : Set X) (hs : MeasurableSet s)
    (F : X × X → ℝ) (hF : Integrable F (ν.prod ν))
    (hsym : ∀ q, F q.swap = F q)
    (hzero : ∀ x ∉ s, ∀ y ∉ s, F (x, y) = 0) :
    (∫ q, F q ∂ν.prod ν) =
      (∫ q, F q ∂(ν.restrict s).prod (ν.restrict s)) +
        2 * (∫ q, F q ∂(ν.restrict s).prod (ν.restrict sᶜ)) := by
  have hss : Integrable F ((ν.restrict s).prod (ν.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hsc : Integrable F ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hcs : Integrable F ((ν.restrict sᶜ).prod (ν.restrict s)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hcc : Integrable F ((ν.restrict sᶜ).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have hmeasure : ν.prod ν =
      ((ν.restrict s).prod (ν.restrict s) + (ν.restrict s).prod (ν.restrict sᶜ)) +
      ((ν.restrict sᶜ).prod (ν.restrict s) + (ν.restrict sᶜ).prod (ν.restrict sᶜ)) := by
    calc
      ν.prod ν = (ν.restrict s + ν.restrict sᶜ).prod (ν.restrict s + ν.restrict sᶜ) := by
        rw [Measure.restrict_add_restrict_compl hs]
      _ = _ := by rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  have hswap : (∫ q, F q ∂(ν.restrict sᶜ).prod (ν.restrict s)) =
      ∫ q, F q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
    simpa only [hsym] using! integral_prod_swap (μ := ν.restrict s) (ν := ν.restrict sᶜ) F
  have hcc0 : (∫ q, F q ∂(ν.restrict sᶜ).prod (ν.restrict sᶜ)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hs.compl),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hx hy
    exact hzero q.1 hx q.2 hy
  rw [hmeasure, integral_add_measure (hss.add_measure hsc) (hcs.add_measure hcc),
    integral_add_measure hss hsc, integral_add_measure hcs hcc, hswap, hcc0]
  ring

theorem rieszInteriorIntegrand_swap {d : ℕ} (m : ℕ) (e : Ambient d)
    (φ : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q.swap = rieszInteriorIntegrand m e φ q := by
  unfold rieszInteriorIntegrand
  dsimp only [Prod.swap]
  rw [kernel_antisymm, inner_neg_right]
  ring

theorem riesz_pairing_split {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [SFinite ν] (s : Set (Ambient d)) (hs : MeasurableSet s)
    (φ : Ambient d → ℝ) (hφzero : ∀ x ∉ s, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Integrable (rieszRawCrossIntegrand m e φ) ((ν.restrict s).prod (ν.restrict sᶜ)) ∧
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂(ν.restrict s).prod (ν.restrict s)) +
          ∫ q, rieszRawCrossIntegrand m e φ q ∂(ν.restrict s).prod (ν.restrict sᶜ) := by
  have hcross : Integrable (rieszInteriorIntegrand m e φ) ((ν.restrict s).prod (ν.restrict sᶜ)) := by
    rw [Measure.prod_restrict]
    exact hF.restrict
  have heq : rieszInteriorIntegrand m e φ =ᵐ[(ν.restrict s).prod (ν.restrict sᶜ)]
      rieszRawCrossIntegrand m e φ := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hs.compl)] with q hy
    unfold rieszInteriorIntegrand rieszRawCrossIntegrand
    rw [hφzero q.2 hy, sub_zero, mul_comm]
  have hsplit := integral_symmetric_pair_split ν s hs (rieszInteriorIntegrand m e φ) hF
    (rieszInteriorIntegrand_swap m e φ) (by
      intro x hx y hy
      simp only [rieszInteriorIntegrand, hφzero x hx, hφzero y hy, sub_self, mul_zero])
  rw [integral_congr_ae heq] at hsplit
  refine ⟨(integrable_congr heq).mp hcross, ?_⟩
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_FinitePairingCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem closedExterior_eq_compl_ball {d : ℕ} (a : Ambient d) (R : ℝ) :
    closedExterior a R = (ball a R)ᶜ := by
  ext y
  change (R ≤ dist a y) ↔ ¬ dist y a < R
  rw [dist_comm y a, not_lt]

theorem center_kernel_integrable_finite_exterior {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R) :
    IntegrableOn (kernel m a) (closedExterior a R) ν := by
  apply Integrable.of_bound (kernel_measurable_right m a).aestronglyMeasurable ((R ^ m)⁻¹)
  filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
  exact kernel_norm_le_truncation m a y R hR hy

theorem riesz_far_integral_eq_raw_of_mean_zero {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0)
    (a : Ambient d) (hk : Integrable (fun y => inner ℝ e (kernel m a y)) η)
    (hraw : Integrable (rieszRawCrossIntegrand m e φ) (ν.prod η)) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod η) ∧
      (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod η) =
        ∫ q, rieszRawCrossIntegrand m e φ q ∂ν.prod η := by
  have hcorrection := hφ.mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q => rieszRawCrossIntegrand m e φ q -
      φ q.1 * inner ℝ e (kernel m a q.2) := by
    funext q
    unfold rieszFarIntegrand rieszRawCrossIntegrand
    rw [inner_sub_right]
    ring
  rw [heq]
  refine ⟨hraw.sub hcorrection, ?_⟩
  rw [integral_sub hraw hcorrection, integral_prod_mul φ (fun y => inner ℝ e (kernel m a y)),
    hzero, zero_mul, sub_zero]

theorem finite_pairing_eq_renormalized {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hφzero : ∀ x ∉ ball a R, φ x = 0)
    (hzero : (∫ x in ball a R, φ x ∂ν) = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Integrable (rieszFarIntegrand m e φ a)
      ((ν.restrict (ball a R)).prod (ν.restrict (closedExterior a R))) ∧
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
        rieszScalarPairing m ν a R e φ := by
  obtain ⟨hraw, hsplit⟩ := riesz_pairing_split m e ν (ball a R) measurableSet_ball φ hφzero hF
  rw [← closedExterior_eq_compl_ball a R] at hraw hsplit
  have hk := Integrable.const_inner (𝕜 := ℝ) e (center_kernel_integrable_finite_exterior m ν a R hR)
  obtain ⟨hfar, heq⟩ := riesz_far_integral_eq_raw_of_mean_zero m e
    (ν.restrict (ball a R)) (ν.restrict (closedExterior a R)) φ hφ.restrict hzero a hk hraw
  refine ⟨hfar, hsplit.trans ?_⟩
  unfold rieszScalarPairing
  dsimp only
  rw [heq]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_OuterPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem outerPairRadius_ge (R : ℝ) (k : ℕ) : R ≤ outerPairRadius R k := by
  unfold outerPairRadius
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem integral_outer_pair_exhaustion {d : ℕ} (ρ : Measure (Ambient d × Ambient d))
    (a : Ambient d) (R : ℝ) (F : Ambient d × Ambient d → ℝ) (hF : Integrable F ρ) :
    Tendsto (fun k : ℕ => ∫ q in univ ×ˢ ball a (outerPairRadius R k), F q ∂ρ)
      atTop (𝓝 (∫ q, F q ∂ρ)) := by
  let s := fun k : ℕ => (univ : Set (Ambient d)) ×ˢ ball a (outerPairRadius R k)
  have hs (k : ℕ) : MeasurableSet (s k) := MeasurableSet.univ.prod measurableSet_ball
  have hmono : Monotone s := by
    intro k l hkl q hq
    refine ⟨hq.1, ?_⟩
    apply (ball_subset_ball ?_) hq.2
    unfold outerPairRadius
    have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hcover : (⋃ k, s k) = univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨k, hk⟩ := exists_nat_gt (dist q.2 a - R)
    apply mem_iUnion.mpr
    refine ⟨k, mem_univ _, ?_⟩
    change dist q.2 a < R + (k : ℝ) + 1
    linarith
  have ht := tendsto_setIntegral_of_monotone hs hmono hF.restrict
  simpa only [hcover, Measure.restrict_univ] using! ht

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_CompactRieszPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compactly supported Lipschitz Riesz pairings

Growth bounds control the exterior pairing of a compactly supported Lipschitz test.
Finite ball restrictions then connect truncated pairings to the renormalized
pairing through the outer-radius limit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszFarIntegrand_integrable_of_compact_lipschitz {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) := by
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν := memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hwL2))
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  have hN := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Filter.Eventually.of_forall hsupport) hweighted _ hZ).1
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ (affineNormalHeight_difference e a 0),
      hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  exact hN

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_PairingLocalizationIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independence of Riesz pairing localization

Exhaustion by outer balls recovers the scalar Riesz pairing from finite restrictions.
For compactly supported mean-zero Lipschitz tests, the resulting pairing is independent
of the localization center and radius satisfying the support separation bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem ball_subset_outer_of_radius_dist {d : ℕ} (a b : Ambient d) (R T : ℝ)
    (h : R + dist a b ≤ T) : ball a R ⊆ ball b T := by
  intro x hx
  change dist x b < T
  change dist x a < R at hx
  have ht := dist_triangle x a b
  linarith

theorem restrict_nested_balls_of_subset {d : ℕ} (μ : Measure (Ambient d))
    (a b : Ambient d) (R T : ℝ) (hsub : ball a R ⊆ ball b T) :
    (μ.restrict (ball b T)).restrict (ball a R) = μ.restrict (ball a R) := by
  rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hsub]

theorem rieszScalarPairing_restrict_outer_ball {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a b : Ambient d) (R T : ℝ)
    (hsub : ball a R ⊆ ball b T) (e : Ambient d) (φ : Ambient d → ℝ) :
    rieszScalarPairing m (μ.restrict (ball b T)) a R e φ =
      (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball b T, rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
  have hcomm : (μ.restrict (ball b T)).restrict (closedExterior a R) =
      (μ.restrict (closedExterior a R)).restrict (ball b T) := by
    rw [Measure.restrict_restrict (closedExterior_measurable a R),
      Measure.restrict_restrict measurableSet_ball, inter_comm]
  have hprod : (μ.restrict (ball a R)).prod ((μ.restrict (closedExterior a R)).restrict (ball b T)) =
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))).restrict (univ ×ˢ ball b T) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold rieszScalarPairing
  dsimp only
  rw [restrict_nested_balls_of_subset μ a b R T hsub, hcomm, hprod]

theorem rieszScalarPairing_outer_limit_at_center {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a b : Ambient d) (R T₀ : ℝ)
    (hcontain : R + dist a b ≤ T₀) (e : Ambient d) (φ : Ambient d → ℝ)
    (hfar : Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    Tendsto (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball b (outerPairRadius T₀ k))) a R e φ)
      atTop (𝓝 (rieszScalarPairing m μ a R e φ)) := by
  have ht := integral_outer_pair_exhaustion
    ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) b T₀
    (rieszFarIntegrand m e φ a) hfar
  have heq : (fun k : ℕ => rieszScalarPairing m (μ.restrict (ball b (outerPairRadius T₀ k))) a R e φ) =
      fun k => (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R))) +
      ∫ q in univ ×ˢ ball b (outerPairRadius T₀ k), rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)) := by
    funext k
    exact rieszScalarPairing_restrict_outer_ball m μ a b R _
      (ball_subset_outer_of_radius_dist a b R _ (hcontain.trans (outerPairRadius_ge T₀ k))) e φ
  rw [heq]
  exact tendsto_const_nhds.add ht

theorem mean_zero_restrict_of_support {d : ℕ} (μ : Measure (Ambient d))
    (φ : Ambient d → ℝ) (a : Ambient d) (R : ℝ)
    (hsupport : ∀ x ∉ ball a R, φ x = 0) (hzero : (∫ x, φ x ∂μ) = 0) :
    (∫ x in ball a R, φ x ∂μ) = 0 :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).trans hzero

theorem rieszScalarPairing_localization_independent {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a b : Ambient d) (H J R S : ℝ) (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hR : 0 < R) (hS : 0 < S) (hHR : 2 * H ≤ R) (hJS : 2 * J ≤ S)
    (hsupportA : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hsupportB : ∀ x, φ x ≠ 0 → dist x b ≤ J)
    (hzero : (∫ x, φ x ∂μ) = 0) :
    rieszScalarPairing (p + 1) μ a R e φ = rieszScalarPairing (p + 1) μ b S e φ := by
  let T₀ := R + S + dist a b
  have hcontainA : R + dist a a ≤ T₀ := by dsimp [T₀]; rw [dist_self]; have := dist_nonneg (x := a) (y := b); linarith
  have hcontainB : S + dist b a ≤ T₀ := by dsimp [T₀]; rw [dist_comm b a]; linarith
  have hfarA := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ a H R hH hR hHR hsupportA
  have hfarB := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ b J S hJ hS hJS hsupportB
  have hlimA := rieszScalarPairing_outer_limit_at_center (p + 1) μ a a R T₀ hcontainA e φ hfarA
  have hlimB := rieszScalarPairing_outer_limit_at_center (p + 1) μ b a S T₀ hcontainB e φ hfarB
  have hφzeroA : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupportA x hn).trans_lt (by linarith : H < R))
  have hφzeroB : ∀ x ∉ ball b S, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupportB x hn).trans_lt (by linarith : J < S))
  have heq : (fun k : ℕ => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius T₀ k))) a R e φ) =
      fun k => rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius T₀ k))) b S e φ := by
    funext k
    let T := outerPairRadius T₀ k
    let ν := μ.restrict (ball a T)
    have hRT₀ : R ≤ T₀ := by simpa only [dist_self, add_zero] using! hcontainA
    have hRT : R ≤ T := hRT₀.trans (outerPairRadius_ge T₀ k)
    have hT : 0 < T := hR.trans_le hRT
    have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T hT
    have hφI : Integrable φ ν := (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a T hT).integrable (by norm_num)
    have hzeroν : (∫ x, φ x ∂ν) = 0 := mean_zero_restrict_of_support μ φ a T
      (fun x hx => hφzeroA x (fun hin => hx ((ball_subset_ball hRT) hin))) hzero
    have hF := rieszInteriorIntegrand_integrable_of_lipschitz p C ν
      (globalGrowth_restrict (p + 1) C μ hg (ball a T)) e φ L hφ (2 * T) (by positivity)
      (ball_restriction_pair_diameter μ a T)
    have hA := (finite_pairing_eq_renormalized (p + 1) e ν a R hR φ hφI hφzeroA
      (mean_zero_restrict_of_support ν φ a R hφzeroA hzeroν) hF).2
    have hB := (finite_pairing_eq_renormalized (p + 1) e ν b S hS φ hφI hφzeroB
      (mean_zero_restrict_of_support ν φ b S hφzeroB hzeroν) hF).2
    exact hA.symm.trans hB
  rw [← heq] at hlimB
  exact tendsto_nhds_unique hlimA hlimB

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OscillationTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem tsupport_subset_ball_of_support_bound {d : ℕ}
    (φ : Ambient d → ℝ) (a : Ambient d) (H A : ℝ) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) : tsupport φ ⊆ ball a A := by
  have hclosed : tsupport φ ⊆ closedBall a H := by
    change closure (Function.support φ) ⊆ closedBall a H
    exact isClosed_closedBall.closure_subset_iff.mpr (fun x hx => hsupport x hx)
  intro x hx
  exact (hclosed hx).trans_lt hHA

theorem ScalarOscillationBound.lipschitz_test_bound {d : ℕ}
    (m : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (A v : ℝ)
    (hosc : ScalarOscillationBound m μ a A v) (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (hsupport : tsupport φ ⊆ ball a A) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing m μ a (2 * A) e φ| ≤ ((D : ℝ) + 1) * v := by
  let c : ℝ := (D : ℝ) + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hscaled := lipschitz_const_mul_real hφ c⁻¹
  have hcoef : ‖c⁻¹‖₊ * D ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    rw [abs_of_pos (inv_pos.mpr hc)]
    have hDc : (D : ℝ) ≤ c := by dsimp [c] <;> linarith
    calc
      c⁻¹ * (D : ℝ) = (D : ℝ) / c := by ring
      _ ≤ 1 := (div_le_one hc).mpr hDc
  have hzero' : (∫ x, c⁻¹ * φ x ∂μ) = 0 := by rw [integral_const_mul, hzero, mul_zero]
  have hb := hosc e he (fun x => c⁻¹ * φ x) (hscaled.weaken hcoef)
    (tsupport_mul_subset_right.trans hsupport) hzero'
  rw [rieszScalarPairing_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hc)] at hb
  calc
    |rieszScalarPairing m μ a (2 * A) e φ| = c * (c⁻¹ * |rieszScalarPairing m μ a (2 * A) e φ|) := by
      field_simp
    _ ≤ c * v := mul_le_mul_of_nonneg_left hb hc.le

theorem oscillation_bound_for_localized_test {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a : Ambient d) (A v : ℝ) (hA : 0 < A) (hosc : ScalarOscillationBound (p + 1) μ a A v)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (φ : Ambient d → ℝ) (D : ℝ≥0) (hφ : LipschitzWith D φ)
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R) (hHA : H < A)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing (p + 1) μ a R e φ| ≤ ((D : ℝ) + 1) * v := by
  have hsupport' : ∀ x, φ x ≠ 0 → dist x a ≤ A := fun x hx => (hsupport x hx).trans hHA.le
  have heq := rieszScalarPairing_localization_independent p C μ hg e φ D hφ a a H A R (2 * A)
    hH hA.le hR (by positivity) hHR le_rfl hsupport hsupport' hzero
  rw [heq]
  exact hosc.lipschitz_test_bound (p + 1) μ a A v e he φ D hφ
    (tsupport_subset_ball_of_support_bound φ a H A hHA hsupport) hzero

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OscillationEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fractional height energy from scalar oscillation

A squared cutoff times a centered Lipschitz height is a mean-zero test with an
explicit Lipschitz bound. Scalar Riesz oscillation controls its pairing; combined
with the ball and shell second-moment estimates, this bounds the fractional
pair energy of the rescaled height on the inner ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem lipschitz_height_bound_on_support {d : ℕ}
    (u χ : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u)
    (a : Ambient d) (H W b T : ℝ) (hW : |u a| ≤ W) (hb : |b| ≤ T)
    (hsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H) :
    ∀ x, χ x ≠ 0 → |u x - b| ≤ W + T + (K : ℝ) * H := by
  intro x hx
  have hdiff : |u x - u a| ≤ (K : ℝ) * dist x a := by
    simpa only [Real.dist_eq] using! hu.dist_le_mul x a
  have hdist := mul_le_mul_of_nonneg_left (hsupport x hx) K.coe_nonneg
  calc
    |u x - b| ≤ |u x - u a| + |u a - b| := abs_sub_le _ _ _
    _ ≤ (K : ℝ) * H + (|u a| + |b|) :=
      add_le_add (hdiff.trans hdist) (by
        simpa only [sub_zero, zero_sub, abs_neg] using! abs_sub_le (u a) 0 b)
    _ ≤ _ := by linarith

theorem centered_height_test_oscillation_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (u χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hu : LipschitzWith K u) (hχ : LipschitzWith L χ) (hχbound : ∀ x, |χ x| ≤ 1)
    (a : Ambient d) (H R A : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hHA : H < A) (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (M c δ W v : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hW : |u a| ≤ W)
    (hcutmass : c ≤ ∫ x in ball a R, χ x ^ 2 ∂μ)
    (hsecond : (∫ x in ball a R, u x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hosc : ScalarOscillationBound (p + 1) μ a A v) :
    |rieszScalarPairing (p + 1) μ a R e
      (fun x => χ x ^ 2 * (u x - cutoffMean (μ.restrict (ball a R)) u χ))| ≤
        ((centeredHeightTestConstant M c H W K L : ℝ) + 1) * v := by
  let ν := μ.restrict (ball a R)
  let b := cutoffMean ν u χ
  let w := fun x => u x - b
  have : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have huL2 := lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a R hR
  have hb : |b| ≤ Real.sqrt (M / c) := cutoffMean_abs_le_uniform ν u χ
    hu.continuous.measurable hχ.continuous.measurable huL2 hχbound c M δ
    hc hM hδ hδ1 hcutmass hsecond
  have hw : LipschitzWith K w := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [w, Real.dist_eq, centered_coordinate_difference] using! hu.dist_le_mul x y
  have hwbound : ∀ x, χ x ≠ 0 → |w x| ≤
      (Real.toNNReal (W + Real.sqrt (M / c) + (K : ℝ) * H) : ℝ) := by
    intro x hx
    exact (lipschitz_height_bound_on_support u χ K hu a H W b (Real.sqrt (M / c))
      hW hb hχsupport x hx).trans (Real.le_coe_toNNReal _)
  have htest := squared_cutoff_height_globally_lipschitz w χ K L
    (Real.toNNReal (W + Real.sqrt (M / c) + (K : ℝ) * H)) hw hχ hχbound hwbound
  have hzeroLocal : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0 :=
    cutoffMean_integral_zero ν u χ hu.continuous.measurable hχ.continuous.measurable
      huL2 hχbound (ne_of_gt (hc.trans_le hcutmass))
  have hzero := squared_cutoff_mean_zero_global μ w χ a H R
    (by linarith) hχsupport hzeroLocal
  have hsupport : ∀ x, χ x ^ 2 * w x ≠ 0 → dist x a ≤ H := by
    intro x hx
    exact hχsupport x (fun hz => hx (by simp only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]))
  exact oscillation_bound_for_localized_test p C μ hg a A v (hH.trans_lt hHA) hosc e he
    (fun x => χ x ^ 2 * w x) (centeredHeightTestConstant M c H W K L) htest
    H R hH hR hHR hHA hsupport hzero

theorem inner_energy_bound_from_oscillation {d : ℕ} (p : ℕ) (C B : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hCB : C * 2 ^ (p + 1) ≤ B)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (u χ : Ambient d → ℝ) (K L : ℝ≥0)
    (hu : LipschitzWith K u) (hχ : LipschitzWith L χ)
    (hcoord : ∀ x y, u x - u y = inner ℝ e (x - y))
    (hχbound : ∀ x, |χ x| ≤ 1) (a : Ambient d) (r H R A : ℝ)
    (hH : 0 ≤ H) (hR : 1 ≤ R) (hHR : 2 * H ≤ R) (hrR : r ≤ R) (hHA : H < A)
    (hχsupport : ∀ x, χ x ≠ 0 → dist x a ≤ H)
    (hχone : ∀ x ∈ ball a r, χ x = 1)
    (M c δ β W : ℝ) (hM : 0 ≤ M) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hβ1 : 1 ≤ β) (hβ2 : β < 2) (hW : |u a| ≤ W)
    (N : ℕ) (hlast : (R * 2 ^ N)⁻¹ ≤ δ)
    (hmass : C * R ^ (p + 1) ≤ M)
    (hcutmass : c ≤ ∫ x in ball a R, χ x ^ 2 ∂μ)
    (hsecond : (∫ x in ball a R, u x ^ 2 ∂μ) ≤ M * δ ^ 2)
    (hshell : ∀ k < N, (∫ y in dyadicAnnulus a R k, u y ^ 2 ∂μ) ≤
      (B * (R * 2 ^ k) ^ (p + 1)) * (δ * (R * 2 ^ k) * β ^ k) ^ 2)
    (hosc : ScalarOscillationBound (p + 1) μ a A (δ ^ 3)) :
    let E := uncenteredEnergyCoefficient p C B M c H R β W
      ((centeredHeightTestConstant M c H W K L : ℝ) + 1) K L
    0 ≤ E ∧
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2)
        ((μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u x / δ) q.1 q.2
          ∂(μ.restrict (ball a r)).prod (μ.restrict (ball a r))) ≤ E := by
  have hsmall := centered_height_test_oscillation_bound p C μ hg e he u χ K L hu hχ hχbound
    a H R A hH (lt_of_lt_of_le zero_lt_one hR) hHR hHA hχsupport
    M c δ W (δ ^ 3) hM hc hδ.le hδ1 hW hcutmass hsecond hosc
  exact uncentered_inner_energy_bound p C B μ hg hCB e u χ K L hu hχ hcoord hχbound
    a r H R hH hR hHR hrR hχsupport hχone M c δ β W
    ((centeredHeightTestConstant M c H W K L : ℝ) + 1) hM hc hδ hδ1 hβ1 hβ2 hW
    (by positivity) N hlast hmass hcutmass hsecond hshell hsmall

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_BoundedRegionTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem radialUnitCutoff_bounds {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d) :
    0 ≤ radialUnitCutoff a R x ∧ radialUnitCutoff a R x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem radialUnitCutoff_eq_one {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : dist x a ≤ R) : radialUnitCutoff a R x = 1 := by
  have h : (1 : ℝ) ≤ R + 1 - dist x a := by linarith
  simp only [radialUnitCutoff, min_eq_left h, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem radialUnitCutoff_support_bound {d : ℕ} (a : Ambient d) (R : ℝ) (x : Ambient d)
    (hx : radialUnitCutoff a R x ≠ 0) : dist x a ≤ R + 1 := by
  by_contra h
  have hneg : R + 1 - dist x a < 0 := by linarith
  have hmin : min 1 (R + 1 - dist x a) ≤ 0 := (min_le_right _ _).trans hneg.le
  exact hx (max_eq_left hmin)

theorem radialUnitCutoff_lipschitz {d : ℕ} (a : Ambient d) (R : ℝ) :
    LipschitzWith 1 (radialUnitCutoff a R) := by
  have h : LipschitzWith 1 (fun x : Ambient d => R + 1 - dist x a) := by
    simpa using! (LipschitzWith.const (R + 1)).sub (LipschitzWith.dist_left a)
  exact (h.const_min 1).const_max 0

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_DyadicSourceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem normalized_second_moment_bound {d : ℕ}
    (μ : Measure (Ambient d)) (u : Ambient d → ℝ) (δ D : ℝ) (hδ : 0 < δ)
    (hbound : (∫ x, u x ^ 2 ∂μ) ≤ δ ^ 2 * D) :
    (∫ x, (u x / δ) ^ 2 ∂μ) ≤ D := by
  simp only [div_pow, integral_div]
  exact (div_le_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa only [mul_comm D] using! hbound)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SourceNormalizedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem source_normalized_second_moments_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (a : Ambient d) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j,
      MemLp (fun x => u j x / δ j) 2 ((μ j).restrict (ball a r)) ∧
      (∫ x in ball a r, (u j x / δ j) ^ 2 ∂μ j) ≤ B := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 2)
  let B₀ := D * ((2 : ℝ) ^ q) ^ n * ((2 : ℝ) ^ q * b ^ q) ^ 2
  have hI (j : ℕ) := normalized_lipschitz_memLp_on_ball n G (μ j) (hg j) (u j) K
    (hu j) a r (δ j) hr
  have hlarge (j : ℕ) := normalized_lipschitz_memLp_on_ball n G (μ j) (hg j) (u j) K
    (hu j) a ((2 : ℝ) ^ q) (δ j) (by positivity)
  have hbound : ∀ᶠ j in atTop, (∫ x in ball a r, (u j x / δ j) ^ 2 ∂μ j) ≤ B₀ := by
    filter_upwards [hN.eventually (eventually_ge_atTop q)] with j hj
    apply (integral_mono_measure
      (Measure.restrict_mono (ball_subset_ball hq.le) le_rfl)
      (Eventually.of_forall fun x => sq_nonneg (u j x / δ j)) (hlarge j).integrable_sq).trans
    apply normalized_second_moment_bound ((μ j).restrict (ball a ((2 : ℝ) ^ q)))
      (u j) (δ j) B₀ (hδ j)
    convert! hsource j q hj using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [B₀]
    ring
  obtain ⟨B, hB, hb⟩ := nonnegative_uniform_bound_of_eventually_le _ B₀ hbound
  exact ⟨B, hB, fun j => ⟨hI j, hb j⟩⟩

theorem source_unnormalized_second_moments_on_ball {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (a : Ambient d) (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ)
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ n * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ M : ℝ, 0 ≤ M ∧ G * r ^ n ≤ M ∧ ∀ j,
      (∫ x in ball a r, u j x ^ 2 ∂μ j) ≤ M * δ j ^ 2 := by
  obtain ⟨B, hB, hb⟩ := source_normalized_second_moments_on_ball n G μ hg u K hu
    a δ hδ N hN D b hsource r hr
  refine ⟨max B (G * r ^ n), hB.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro j
  have h := (hb j).2
  simp only [div_pow, integral_div] at h
  exact ((div_le_iff₀ (sq_pos_of_pos (hδ j))).mp h).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_SourceRadialCutoffMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Lower mass bounds for radial cutoffs

A radial cutoff equal to one on a smaller ball transfers its mass lower bound to
the squared-cutoff integral on a larger ball. For source measures with growing
support diameters, the prescribed lower growth estimate supplies this bound eventually.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem radial_cutoff_mass_of_ball_mass {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R c : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hc : 0 ≤ c)
    (hmass : ENNReal.ofReal c ≤ μ (ball a r)) :
    c ≤ ∫ x in ball a R, (radialUnitCutoff a r x) ^ 2 ∂μ := by
  let := finiteMeasure_restrict_ball_of_globalGrowth n G μ hg a R (hr.trans_le hrR)
  have hfin : μ (ball a r) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hg.2 a r hr)
  have hreal : c ≤ (μ (ball a r)).toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).mpr hmass
    simpa only [ENNReal.toReal_ofReal hc] using! h
  have hcut := cutoff_mass_lower_of_one_on (μ.restrict (ball a R))
    (radialUnitCutoff a r) (radialUnitCutoff_lipschitz a r).continuous.measurable
    (fun x => by
      rw [abs_of_nonneg (radialUnitCutoff_bounds a r x).1]
      exact (radialUnitCutoff_bounds a r x).2)
    (ball a r) measurableSet_ball (fun x hx => radialUnitCutoff_eq_one a r x hx.le)
  have hrestrict : (μ.restrict (ball a R)).real (ball a r) = (μ (ball a r)).toReal := by
    rw [Measure.real, Measure.restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball hrR)]
  rw [hrestrict] at hcut
  exact hreal.trans hcut

theorem source_radial_cutoff_mass_eventually {d : ℕ} (n : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (a : Ambient d) (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball a r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ∀ᶠ j in atTop, r ^ n / C ≤
      ∫ x in ball a R, (radialUnitCutoff a r x) ^ 2 ∂μ j := by
  filter_upwards [hdiam r hr] with j hj
  exact radial_cutoff_mass_of_ball_mass n G (μ j) (hg j) a r R (r ^ n / C)
    hr hrR (by positivity) (hlower j r ⟨hr, hj⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_SourceNormalizedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform energy of normalized source heights

Dyadic second-moment bounds and vanishing oscillation control the fractional pair
energy of normalized affine heights on each fixed ball. Eventual estimates extend
to a nonnegative bound for the whole sequence, with integrability retained.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_normalized_energy_on_ball {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (a : Ambient d) (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball a r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (u : ℕ → Ambient d → ℝ) (K : ℝ≥0) (hu : ∀ j, LipschitzWith K (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (W : ℝ) (hW : ∀ j, |u j a| ≤ W)
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (δ j ^ 3))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball a ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2)
    (r : ℝ) (hr : 0 < r) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ j,
      Integrable (fun q : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
        (((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
          ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E := by
  let : ∀ j, IsFiniteMeasureOnCompacts (μ j) := fun j => (hg j).finite_on_compacts
  let H := r + 1
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (max 1 (2 * H)) (by norm_num : (1 : ℝ) < 2)
  let R : ℝ := 2 ^ q
  have hR : 1 ≤ R := (le_max_left _ _).trans hq.le
  have hHR : 2 * H ≤ R := (le_max_right _ _).trans hq.le
  have hH : 0 ≤ H := by dsimp [H] <;> linarith
  have hrR : r ≤ R := by dsimp [H] at hHR <;> linarith
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let c : ℝ := r ^ (p + 1) / C
  have hc : 0 < c := by dsimp [c] <;> positivity
  obtain ⟨M, hM, hmass, hsecond⟩ := source_unnormalized_second_moments_on_ball
    (p + 1) G μ hg u K hu a δ hδ N hN D b hsource R hRpos
  have huL2 (l j : ℕ) : MemLp (u j) 2 ((μ j).restrict (ball a ((2 : ℝ) ^ l))) :=
    lipschitz_height_memLp_on_ball (p + 1) G (μ j) (hg j) (u j) K (hu j)
      a ((2 : ℝ) ^ l) (by positivity)
  obtain ⟨B, hGB, hshell⟩ := controlled_shell_moments_from_dyadic_balls
    (p + 1) μ a u δ N D b (G * 2 ^ (p + 1)) huL2 hsource q
  have hshift := (dyadic_shifted_last_error_tendsto q N δ hN hlast).2
  have hcut := source_radial_cutoff_mass_eventually (p + 1) C G μ hg a hC
    hlower hdiam r R hr hrR
  let χ := radialUnitCutoff a r
  have hχbound (x : Ambient d) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (radialUnitCutoff_bounds a r x).1]
    exact (radialUnitCutoff_bounds a r x).2
  let E := uncenteredEnergyCoefficient p G B M c H R b W
    ((centeredHeightTestConstant M c H W K 1 : ℝ) + 1) K 1
  have hE : ∀ᶠ j in atTop,
      (∫ v : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => u j x / δ j) v.1 v.2
          ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E := by
    filter_upwards [hcut, hδlim.eventually (gt_mem_nhds zero_lt_one),
      hA.eventually (eventually_gt_atTop H), hshift.eventually (gt_mem_nhds zero_lt_one)]
      with j hjcut hjδ hjA hjlast
    have hlastj : (R * 2 ^ (N j - (q + 1)))⁻¹ ≤ δ j := by
      exact ((div_lt_iff₀ (hδ j)).mp hjlast).le.trans_eq (one_mul _)
    have h := inner_energy_bound_from_oscillation p G B (μ j) (hg j) hGB (z j) (hz j)
      (u j) χ K 1 (hu j) (radialUnitCutoff_lipschitz a r) (hdiff j) hχbound
      a r H R (A j) hH hR hHR hrR hjA
      (fun x hx => radialUnitCutoff_support_bound a r x hx)
      (fun x hx => radialUnitCutoff_eq_one a r x hx.le)
      M c (δ j) b W hM hc (hδ j) hjδ.le hb1 hb2 (hW j)
      (N j - (q + 1)) hlastj hmass hjcut (hsecond j) (hshell j) (hosc j)
    exact h.2.2
  obtain ⟨E', hE', hb⟩ := nonnegative_uniform_bound_of_eventually_le _ E hE
  exact ⟨E', hE', fun j =>
    ⟨normalized_lipschitz_energy_integrable_on_ball p G (μ j) (hg j) (u j) K (hu j)
      a r (δ j) hr, hb j⟩⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_NormalCoordinateTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open WithLp
open scoped NNReal

theorem normalDirection_norm {q d : ℕ} (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    ‖normalDirection N i‖ = 1 := by
  rw [normalDirection, N.norm_map]
  exact (EuclideanSpace.basisFun (Fin q) ℝ).norm_eq_one i

theorem normalCoordinate_eq_inner {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x : Ambient d) :
    normalCoordinate a N i x = inner ℝ (normalDirection N i) (x - a) := by
  calc
    _ = inner ℝ (EuclideanSpace.basisFun (Fin q) ℝ i)
        (N.toContinuousLinearMap.adjoint (x - a)) :=
      (EuclideanSpace.basisFun_inner (Fin q) ℝ (N.toContinuousLinearMap.adjoint (x - a)) i).symm
    _ = _ := N.toContinuousLinearMap.adjoint_inner_right _ _

theorem normalCoordinate_difference {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) (x y : Ambient d) :
    normalCoordinate a N i x - normalCoordinate a N i y = inner ℝ (normalDirection N i) (x - y) := by
  rw [normalCoordinate_eq_inner, normalCoordinate_eq_inner, ← inner_sub_right,
    sub_sub_sub_cancel_right]

theorem normalCoordinate_lipschitz {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) : LipschitzWith 1 (normalCoordinate a N i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, normalCoordinate_difference, dist_eq_norm]
  have h := abs_real_inner_le_norm (normalDirection N i) (x - y)
  simpa only [normalDirection_norm, one_mul] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_NormalFrameSourceEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Source energy in a normal frame

Convergence of frame centers gives a common bound for their normal coordinates at
the origin. Applying the scalar source estimates coordinatewise supplies local L²
and fractional pair-energy bounds for normalized normal heights on every fixed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem normalCoordinate_abs_at_zero_le_norm {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    |normalCoordinate a N i 0| ≤ ‖a‖ := by
  rw [normalCoordinate_eq_inner]
  simpa only [normalDirection_norm, one_mul, zero_sub, norm_neg] using!
    abs_real_inner_le_norm (normalDirection N i) ((0 : Ambient d) - a)

theorem normalCoordinates_uniform_center_bound {q d : ℕ}
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ j i, |normalCoordinate (a j) (N j) i 0| ≤ W := by
  have hn : Tendsto (fun j => ‖a j‖) atTop (𝓝 0) := by simpa only [norm_zero] using! ha.norm
  have hb : ∀ᶠ j in atTop, ‖a j‖ ≤ 1 :=
    (hn.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le
  obtain ⟨W, hW, hw⟩ := nonnegative_uniform_bound_of_eventually_le _ 1 hb
  exact ⟨W, hW, fun j i => (normalCoordinate_abs_at_zero_le_norm (a j) (N j) i).trans (hw j)⟩

theorem normal_frame_source_data_on_ball_oai {q d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball 0 r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ i j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ j) ≤
        δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∀ i : Fin q, ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
      MemLp (fun x => normalCoordinate (a j) (N j) i x / δ j) 2 ((μ j).restrict (ball 0 r)) ∧
      (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ j) ^ 2 ∂μ j) ≤ B ∧
      Integrable (fun v : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2)
        (((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ∧
      (∫ v : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2
          ∂((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ≤ E := by
  obtain ⟨W, _hW, hw⟩ := normalCoordinates_uniform_center_bound a ha N
  intro i r hr
  obtain ⟨B, hB, hm⟩ := source_normalized_second_moments_on_ball (p + 1) G μ hg
    (fun j => normalCoordinate (a j) (N j) i) 1
    (fun j => normalCoordinate_lipschitz (a j) (N j) i)
    0 δ hδ T hT D b (hsource i) r hr
  obtain ⟨E, hE, he⟩ := source_normalized_energy_on_ball p C G μ hg 0 hC hlower hdiam
    (fun j => normalCoordinate (a j) (N j) i) 1
    (fun j => normalCoordinate_lipschitz (a j) (N j) i)
    (fun j => normalDirection (N j) i) (fun j => (normalDirection_norm (N j) i).le)
    (fun j => normalCoordinate_difference (a j) (N j) i) W (fun j => hw j i)
    δ A hδ hδlim hA hosc T hT D b hb1 hb2 hlast (hsource i) r hr
  exact ⟨B, E, hB, hE, fun j => ⟨(hm j).1, (hm j).2, (he j).1, (he j).2⟩⟩

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.normal_frame_source_data_on_ball_oai := @OAI.RieszRectifiability.normal_frame_source_data_on_ball_oai
