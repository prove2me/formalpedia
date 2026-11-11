-- Prove2me | solution 1 for OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:50.07225+00:00
-- url     : https://prove2.me/submissions/3f6e8030-1126-40bc-a140-a663867f8759

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

theorem kernel_self {d : ℕ} (n : ℕ) (x : Ambient d) : kernel n x x = 0 := by
  simp [kernel]

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_PlanarPullbackMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pullback along the adjoint of an isometric embedding transports a measure supported on
its range to Euclidean coordinates, preserving ball masses and upper growth bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem globalGrowth_finite_on_compacts {n d : ℕ} (C : ℝ)
    (ν : Measure (Ambient d)) (hg : GlobalUpperGrowth n C ν) : IsFiniteMeasureOnCompacts ν := by
  let : IsLocallyFiniteMeasure ν := ⟨fun x => ⟨ball x 1, ball_mem_nhds x zero_lt_one,
    (hg.2 x 1 zero_lt_one).trans_lt ENNReal.ofReal_lt_top⟩⟩
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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_FiniteWeightedSchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem weighted_young_real (x y u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * x * y ≤ x ^ 2 * v / u + y ^ 2 * u / v := by
  have heq : (x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y) * (u * v) =
      (v * x - u * y) ^ 2 := by
    field_simp
    ring
  have hp := sq_nonneg (v * x - u * y)
  rw [← heq] at hp
  have hnonneg : 0 ≤ x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y :=
    nonneg_of_mul_nonneg_left hp (mul_pos hu hv)
  linarith

theorem finite_weighted_schur_quadratic {ι : Type*} (s : Finset ι)
    (k : ι → ι → ℝ) (w a : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hk : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ k i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, k j i = k i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, k i j * w j ≤ C * w i) :
    (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ C * ∑ i ∈ s, a i ^ 2 := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      2 * (|a i| * |a j| * k i j) ≤
        a i ^ 2 * k i j * w j / w i + a j ^ 2 * k i j * w i / w j := by
    have hy := weighted_young_real |a i| |a j| (w i) (w j) (hw i hi) (hw j hj)
    simp only [sq_abs] at hy
    calc
      _ = (2 * |a i| * |a j|) * k i j := by ring
      _ ≤ (a i ^ 2 * w j / w i + a j ^ 2 * w i / w j) * k i j :=
        mul_le_mul_of_nonneg_right hy (hk i hi j hj)
      _ = _ := by ring
  let A : ℝ := ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * k i j * w j / w i
  let B : ℝ := ∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * k i j * w i / w j
  have hA : A ≤ C * ∑ i ∈ s, a i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = (a i ^ 2 / w i) * (∑ j ∈ s, k i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (a i ^ 2 / w i) * (C * w i) :=
        mul_le_mul_of_nonneg_left (hrow i hi) (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = C * a i ^ 2 := by field_simp [(hw i hi).ne']
  have hBA : B = A := by
    dsimp only [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm i hi j hj]
  have hh := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
  have htwo : 2 * (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ A + B := by
    simpa only [A, B, Finset.sum_add_distrib, Finset.mul_sum] using! hh
  rw [hBA] at htwo
  linarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_WeightedGramBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem finite_synthesis_sq_le_weighted_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (h : ι → E) (w a : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ (h i) (h j)| * w j ≤ C * w i) :
    ‖∑ i ∈ s, a i • h i‖ ^ 2 ≤ C * ∑ i ∈ s, a i ^ 2 := by
  have heq : ‖∑ i ∈ s, a i • h i‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * inner ℝ (h i) (h j) := by
    rw [← real_inner_self_eq_norm_sq]
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * |inner ℝ (h i) (h j)| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul] using! le_abs_self (a i * a j * inner ℝ (h i) (h j))
    _ ≤ _ := finite_weighted_schur_quadratic s (fun i j => |inner ℝ (h i) (h j)|) w a C hw
      (fun _ _ _ _ => abs_nonneg _) (fun i _ j _ => by rw [real_inner_comm]) hrow

theorem finite_bessel_of_weighted_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (s : Finset ι) (h : ι → E) (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ (h i) (h j)| * w j ≤ C * w i) (u : E) :
    ∑ i ∈ s, (inner ℝ (h i) u) ^ 2 ≤ C * ‖u‖ ^ 2 := by
  let a := fun i => inner ℝ (h i) u
  let S : ℝ := ∑ i ∈ s, a i ^ 2
  let v := ∑ i ∈ s, a i • h i
  have hSv : inner ℝ v u = S := by
    simp only [v, S, a, sum_inner, real_inner_smul_left, pow_two]
  have hv : ‖v‖ ^ 2 ≤ C * S := finite_synthesis_sq_le_weighted_gram s h w a C hw hrow
  have hcs := real_inner_mul_inner_self_le v u
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hSv] at hcs
  have hcs' : S ^ 2 ≤ ‖v‖ ^ 2 * ‖u‖ ^ 2 := by simpa only [pow_two] using! hcs
  have hsq : S ^ 2 ≤ C * S * ‖u‖ ^ 2 := by
    exact hcs'.trans (mul_le_mul_of_nonneg_right hv (sq_nonneg ‖u‖))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change S ≤ C * ‖u‖ ^ 2
  by_cases hzero : S = 0
  · rw [hzero]
    exact mul_nonneg hC (sq_nonneg _)
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    nlinarith

theorem finite_L2_bessel_of_weighted_pairings {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (w : ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ i ∈ s, 0 < w i)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |∫ x, f i x * f j x ∂μ| * w j ≤ C * w i)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ C * ∫ x, u x ^ 2 ∂μ := by
  have hGram : ∀ i ∈ s, ∑ j ∈ s, |inner ℝ ((hf i).toLp (f i)) ((hf j).toLp (f j))| * w j ≤ C * w i := by
    simpa only [toLp_inner_eq_integral] using! hrow
  have hb := finite_bessel_of_weighted_gram s (fun i => (hf i).toLp (f i)) w C hC hw hGram (hu.toLp u)
  simpa only [toLp_inner_eq_integral, toLp_norm_sq_eq_integral] using! hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_MeanZeroGramDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mean-zero pairing decay

Cancellation against constants turns Lipschitz control into a radius gain for pairings
with mean-zero functions. Support-ball mass and growth bounds further control these
pairings in terms of the support radius and the uniform size of the mean-zero function.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal

theorem mean_zero_lipschitz_pairing_bound {d : ℕ} (μ : Measure (Ambient d))
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d) (R : ℝ)
    (hs : ∀ x, g x ≠ 0 → dist x z ≤ R) :
    |∫ x, f x * g x ∂μ| ≤ (L : ℝ) * R * ∫ x, |g x| ∂μ := by
  have hfg : Integrable (fun x => f x * g x) μ := memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hf) (hf := hg))
  have hsub : Integrable (fun x => (f x - f z) * g x) μ := by
    simpa only [sub_mul] using! hfg.sub (hgI.const_mul (f z))
  have heq : (∫ x, (f x - f z) * g x ∂μ) = ∫ x, f x * g x ∂μ := by
    simp only [sub_mul]
    rw [integral_sub hfg (hgI.const_mul (f z)), integral_const_mul, hzero, mul_zero, sub_zero]
  rw [← heq]
  calc
    _ ≤ ∫ x, |(f x - f z) * g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, ((L : ℝ) * R) * |g x| ∂μ := by
      apply integral_mono hsub.abs (hgI.abs.const_mul _)
      intro x
      change |(f x - f z) * g x| ≤ (L : ℝ) * R * |g x|
      by_cases hx : g x = 0
      · simp only [hx, mul_zero, abs_zero, le_refl]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have h := hLip.dist_le_mul x z
      rw [Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hs x hx) L.coe_nonneg)
    _ = _ := integral_const_mul _ _

theorem integral_abs_le_support_ball_mass {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (g : Ambient d → ℝ) (hg : Integrable g μ)
    (z : Ambient d) (R A : ℝ) (hbound : ∀ x, |g x| ≤ A)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z R) :
    (∫ x, |g x| ∂μ) ≤ A * μ.real (ball z R) := by
  have : IsFiniteMeasure (μ.restrict (ball z R)) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall z R).measure_lt_top))
  have heq : (∫ x in ball z R, |g x| ∂μ) = ∫ x, |g x| ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : g x = 0 := by by_contra hn; exact hx (hs x hn)
    rw [hz, abs_zero]
  rw [← heq]
  calc
    _ ≤ ∫ _x in ball z R, A ∂μ := integral_mono hg.abs.restrict (integrable_const _)
      (fun x => hbound x)
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm]

theorem compact_lipschitz_test_memLp {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : Ambient d → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (z : Ambient d) (R : ℝ) (hs : tsupport f ⊆ ball z R) :
    MemLp f 2 μ ∧ Integrable f μ := by
  have hc : HasCompactSupport f :=
    (isCompact_closedBall z R).of_isClosed_subset (isClosed_tsupport f) (hs.trans ball_subset_closedBall)
  exact ⟨hLip.continuous.memLp_of_hasCompactSupport hc,
    hLip.continuous.integrable_of_hasCompactSupport hc⟩

theorem mean_zero_gram_bound_of_growth {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d) (R A : ℝ)
    (hR : 0 < R) (hA : 0 ≤ A) (hbound : ∀ x, |g x| ≤ A)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z R) :
    |∫ x, f x * g x ∂μ| ≤ ((L : ℝ) * R * A) * (G * R ^ n) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hgrowth
  have hm : μ.real (ball z R) ≤ G * R ^ n :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hgrowth.1 (pow_nonneg hR.le n))
      (hgrowth.2 z R hR)
  calc
    _ ≤ (L : ℝ) * R * ∫ x, |g x| ∂μ := mean_zero_lipschitz_pairing_bound μ f g hf hg hgI hzero
      L hLip z R (fun x hx => (hs x hx).le)
    _ ≤ (L : ℝ) * R * (A * (G * R ^ n)) :=
      mul_le_mul_of_nonneg_left ((integral_abs_le_support_ball_mass μ g hgI z R A hbound hs).trans
        (mul_le_mul_of_nonneg_left hm hA)) (mul_nonneg L.coe_nonneg hR.le)
    _ = _ := by ring

theorem integral_pairing_zero_of_disjoint_support {d : ℕ} (μ : Measure (Ambient d))
    (f g : Ambient d → ℝ) (hs : Disjoint (Function.support f) (Function.support g)) :
    (∫ x, f x * g x ∂μ) = 0 := by
  have hz : (fun x => f x * g x) = 0 := by
    funext x
    by_cases hf : f x = 0
    · simp only [hf, zero_mul, Pi.zero_apply]
    · have hg : g x = 0 := by
        by_contra hg
        exact Set.disjoint_left.mp hs hf hg
      simp only [hg, mul_zero, Pi.zero_apply]
  rw [hz]
  change (∫ _x : Ambient d, (0 : ℝ) ∂μ) = 0
  exact integral_zero _ _

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_ADCoreMassPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Function

theorem finite_disjoint_core_mass_bound {ι : Type*} {d : ℕ}
    (n : ℕ) (G : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (s : Finset ι) (z : ι → Ambient d) (ρ mass : ι → ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, ENNReal.ofReal (mass i) ≤ μ (ball (z i) (ρ i)))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hsub : ∀ i ∈ s, ball (z i) (ρ i) ⊆ ball a R)
    (hdisjoint : Set.PairwiseDisjoint (s : Set ι) (fun i => ball (z i) (ρ i))) :
    ∑ i ∈ s, mass i ≤ G * R ^ n := by
  have hs : ENNReal.ofReal (∑ i ∈ s, mass i) ≤ ENNReal.ofReal (G * R ^ n) := by
    calc
      _ = ∑ i ∈ s, ENNReal.ofReal (mass i) := ENNReal.ofReal_sum_of_nonneg hmass
      _ ≤ ∑ i ∈ s, μ (ball (z i) (ρ i)) := Finset.sum_le_sum hlower
      _ = μ (⋃ i ∈ s, ball (z i) (ρ i)) :=
        (measure_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)).symm
      _ ≤ μ (ball a R) := measure_mono (iUnion₂_subset hsub)
      _ ≤ _ := hg.2 a R hR
  have hr := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hR.le n)) hs
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg hmass)] using! hr

theorem finite_AD_core_mass_packing {ι : Type*} {d : ℕ}
    (n : ℕ) (C G : ℝ) (hC : 0 < C) (μ : Measure (Ambient d))
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (s : Finset ι) (z : ι → Ambient d) (r : ι → ℝ) (c : ℝ) (hc : 0 < c)
    (hz : ∀ i ∈ s, z i ∈ μ.support) (hr : ∀ i ∈ s, 0 < r i)
    (hadmissible : ∀ i ∈ s, AdmissibleRadius μ (c * r i))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hcontained : ∀ i ∈ s, dist (z i) a + c * r i ≤ R)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c * r i + c * r j ≤ dist (z i) (z j)) :
    ∑ i ∈ s, (r i) ^ n ≤ (C / c ^ n) * (G * R ^ n) := by
  have hd : Set.PairwiseDisjoint (s : Set ι) (fun i => ball (z i) (c * r i)) := by
    intro i hi j hj hij
    exact ball_disjoint_ball (hsep i hi j hj hij)
  have hsub : ∀ i ∈ s, ball (z i) (c * r i) ⊆ ball a R := by
    intro i hi
    apply ball_subset_ball'
    linarith [hcontained i hi]
  have hb := finite_disjoint_core_mass_bound n G μ hg s z (fun i => c * r i)
    (fun i => (c * r i) ^ n / C) (fun i hi => by have hri := hr i hi; positivity)
    (fun i hi => hlower (z i) (hz i hi) (c * r i) (hadmissible i hi)) a R hR hsub hd
  have heq : (∑ i ∈ s, (c * r i) ^ n / C) = (c ^ n / C) * ∑ i ∈ s, r i ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow]
    ring
  rw [heq] at hb
  have hcoef : 0 < c ^ n / C := div_pos (pow_pos hc n) hC
  have h : (∑ i ∈ s, r i ^ n) ≤ (G * R ^ n) / (c ^ n / C) :=
    (le_div_iff₀ hcoef).mpr (by simpa only [mul_comm] using! hb)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_GeometricGramRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem finite_row_bound_of_geometric_slices {ι : Type*} (s : Finset ι)
    (gap : ι → ℕ) (v : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hslice : ∀ k : ℕ, ∑ j ∈ s with gap j = k, v j ≤ A * (1 / 2 : ℝ) ^ k) :
    ∑ j ∈ s, v j ≤ 2 * A := by
  classical
  have hsum : (∑ k ∈ s.image gap, ∑ j ∈ s with gap j = k, v j) = ∑ j ∈ s, v j :=
    Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem gap hj) v
  rw [← hsum]
  calc
    _ ≤ ∑ k ∈ s.image gap, A * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum (fun k _ => hslice k)
    _ = A * ∑ k ∈ s.image gap, (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left (finite_geometric_two_sum_le _) hA
    _ = _ := by ring

theorem finite_L2_bessel_of_geometric_gram_slices {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (w : ι → ℝ) (gap : ι → ι → ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ i ∈ s, 0 < w i)
    (hslice : ∀ i ∈ s, ∀ k : ℕ,
      ∑ j ∈ s with gap i j = k, |∫ x, f i x * f j x ∂μ| * w j ≤
        A * w i * (1 / 2 : ℝ) ^ k)
    (u : X → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, f i x * u x ∂μ) ^ 2 ≤ (2 * A) * ∫ x, u x ^ 2 ∂μ := by
  refine finite_L2_bessel_of_weighted_pairings μ s f hf w (2 * A) (by positivity) hw ?_ u hu
  intro i hi
  have h := finite_row_bound_of_geometric_slices s (gap i)
    (fun j => |∫ x, f i x * f j x ∂μ| * w j) (A * w i)
    (mul_nonneg hA (hw i hi).le) (hslice i hi)
  simpa only [mul_assoc] using! h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_NormalizedGramDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem normalized_mean_zero_gram_decay {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d)
    (ri rj wi wj J A : ℝ) (hri : 0 < ri) (hrj : 0 < rj) (hwi : 0 < wi) (hwj : 0 < wj)
    (hJ : 0 < J) (hA : 0 ≤ A) (hwjSq : wj ^ 2 = rj ^ n)
    (hL : (L : ℝ) ≤ A / (ri * wi)) (hbound : ∀ x, |g x| ≤ A / wj)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z (J * rj)) :
    |∫ x, f x * g x ∂μ| ≤ (G * J ^ (n + 1) * A ^ 2) * (rj / ri) * (wj / wi) := by
  have hraw := mean_zero_gram_bound_of_growth n G μ hgrowth f g hf hg hgI hzero L hLip
    z (J * rj) (A / wj) (mul_pos hJ hrj) (div_nonneg hA hwj.le) hbound hs
  calc
    _ ≤ ((L : ℝ) * (J * rj) * (A / wj)) * (G * (J * rj) ^ n) := hraw
    _ = (L : ℝ) * ((J * rj) * (A / wj) * (G * (J * rj) ^ n)) := by ring
    _ ≤ (A / (ri * wi)) * ((J * rj) * (A / wj) * (G * (J * rj) ^ n)) :=
      mul_le_mul_of_nonneg_right hL (by have hG := hgrowth.1; positivity)
    _ = _ := by
      rw [mul_pow, ← hwjSq, pow_succ]
      field_simp
      ring

theorem normalized_gram_fine_weighted {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hgI : Integrable g μ) (hzero : (∫ x, g x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (z : Ambient d)
    (ri rj wi wj J A : ℝ) (hri : 0 < ri) (hrj : 0 < rj) (hwi : 0 < wi) (hwj : 0 < wj)
    (hJ : 0 < J) (hA : 0 ≤ A) (hwjSq : wj ^ 2 = rj ^ n)
    (hL : (L : ℝ) ≤ A / (ri * wi)) (hbound : ∀ x, |g x| ≤ A / wj)
    (hs : ∀ x, g x ≠ 0 → x ∈ ball z (J * rj)) :
    |∫ x, f x * g x ∂μ| * wj ≤ (G * J ^ (n + 1) * A ^ 2) * (rj / ri) * (wj ^ 2 / wi) := by
  have h := mul_le_mul_of_nonneg_right
    (normalized_mean_zero_gram_decay n G μ hgrowth f g hf hg hgI hzero L hLip z
      ri rj wi wj J A hri hrj hwi hwj hJ hA hwjSq hL hbound hs) hwj.le
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem normalized_gram_coarse_weighted {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth n G μ)
    (f g : Ambient d → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfI : Integrable f μ) (hzero : (∫ x, f x ∂μ) = 0)
    (L : ℝ≥0) (hLip : LipschitzWith L g) (z : Ambient d)
    (ri rj wi wj J A : ℝ) (hri : 0 < ri) (hrj : 0 < rj) (hwi : 0 < wi) (hwj : 0 < wj)
    (hJ : 0 < J) (hA : 0 ≤ A) (hwiSq : wi ^ 2 = ri ^ n)
    (hL : (L : ℝ) ≤ A / (rj * wj)) (hbound : ∀ x, |f x| ≤ A / wi)
    (hs : ∀ x, f x ≠ 0 → x ∈ ball z (J * ri)) :
    |∫ x, f x * g x ∂μ| * wj ≤ (G * J ^ (n + 1) * A ^ 2) * (ri / rj) * wi := by
  have h := mul_le_mul_of_nonneg_right
    (normalized_mean_zero_gram_decay n G μ hgrowth g f hg hf hfI hzero L hLip z
      rj ri wj wi J A hrj hri hwj hwi hJ hA hwiSq hL hbound hs) hwj.le
  have heq : (∫ x, g x * f x ∂μ) = ∫ x, f x * g x ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
  rw [heq] at h
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

theorem nonzero_gram_centers_near {d : ℕ} (μ : Measure (Ambient d))
    (f g : Ambient d → ℝ) (a b : Ambient d) (R S : ℝ)
    (hf : ∀ x, f x ≠ 0 → x ∈ ball a R) (hg : ∀ x, g x ≠ 0 → x ∈ ball b S)
    (hne : (∫ x, f x * g x ∂μ) ≠ 0) : dist a b < R + S := by
  have hnd : ¬ Disjoint (Function.support f) (Function.support g) := by
    intro hd
    exact hne (integral_pairing_zero_of_disjoint_support μ f g hd)
  obtain ⟨x, hxf, hxg⟩ := Set.not_disjoint_iff.mp hnd
  have ha := hf x hxf
  have hb := hg x hxg
  have hax : dist a x < R := by simpa only [mem_ball, dist_comm] using! ha
  exact (dist_triangle a x b).trans_lt (add_lt_add hax hb)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_ADInteractionPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem finite_AD_fine_interaction_mass {ι : Type*} {d : ℕ}
    (n : ℕ) (C G : ℝ) (hC : 0 < C) (μ : Measure (Ambient d))
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (s : Finset ι) (z : ι → Ambient d) (r : ι → ℝ) (c J : ℝ) (hc : 0 < c) (hJ : 0 < J)
    (hz : ∀ i ∈ s, z i ∈ μ.support) (hr : ∀ i ∈ s, 0 < r i)
    (hadmissible : ∀ i ∈ s, AdmissibleRadius μ (c * r i))
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (hsmall : ∀ i ∈ s, r i ≤ R)
    (hnear : ∀ i ∈ s, dist (z i) a ≤ J * R + J * r i)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c * r i + c * r j ≤ dist (z i) (z j)) :
    ∑ i ∈ s, (r i) ^ n ≤ interactionPackingConstant n C G c J * R ^ n := by
  have hcontained : ∀ i ∈ s, dist (z i) a + c * r i ≤ (2 * J + c) * R := by
    intro i hi
    have hjr := mul_le_mul_of_nonneg_left (hsmall i hi) hJ.le
    have hcr := mul_le_mul_of_nonneg_left (hsmall i hi) hc.le
    linarith [hnear i hi]
  have h := finite_AD_core_mass_packing n C G hC μ hg hlower s z r c hc hz hr hadmissible
    a ((2 * J + c) * R) (by positivity) hcontained hsep
  simpa only [interactionPackingConstant, mul_pow, mul_assoc] using! h

theorem finite_AD_coarse_interaction_card {ι : Type*} {d : ℕ}
    (n : ℕ) (C G : ℝ) (hC : 0 < C) (μ : Measure (Ambient d))
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (s : Finset ι) (z : ι → Ambient d) (q c J : ℝ) (hq : 0 < q) (hc : 0 < c) (hJ : 0 < J)
    (hz : ∀ i ∈ s, z i ∈ μ.support) (hadmissible : AdmissibleRadius μ (c * q))
    (a : Ambient d) (R : ℝ) (hRq : R ≤ q)
    (hnear : ∀ i ∈ s, dist (z i) a ≤ J * R + J * q)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → c * q + c * q ≤ dist (z i) (z j)) :
    (s.card : ℝ) ≤ interactionPackingConstant n C G c J := by
  have hnear' : ∀ i ∈ s, dist (z i) a ≤ J * q + J * q := by
    intro i hi
    exact (hnear i hi).trans (add_le_add (mul_le_mul_of_nonneg_left hRq hJ.le) le_rfl)
  have h := finite_AD_fine_interaction_mass n C G hC μ hg hlower s z (fun _ => q) c J hc hJ
    hz (fun _ _ => hq) (fun _ _ => hadmissible) a q hq (fun _ _ => le_rfl) hnear' hsep
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  exact (mul_le_mul_iff_left₀ (pow_pos hq n)).mp h

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_DyadicLipschitzFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalized dyadic Lipschitz test families

The family packages mean-zero compactly supported tests with dyadic radii, separated
centers, and weights whose squares are the dimensional powers of the radii.
Its support and regularity assumptions give integrability, while global upper growth
gives weighted Gram estimates at both finer and coarser scales.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicLipschitzFamily.memLp_integrable {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} [IsFiniteMeasureOnCompacts μ] {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i : ι) : MemLp (F.test i) 2 μ ∧ Integrable (F.test i) μ :=
  compact_lipschitz_test_memLp μ (F.test i) (F.lip i) (F.lipschitz i)
    (F.center i) (J * F.radius i) (F.support_subset i)

theorem DyadicLipschitzFamily.support_ball {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i : ι) (x : Ambient d) (hx : F.test i x ≠ 0) :
    x ∈ ball (F.center i) (J * F.radius i) :=
  F.support_subset i (subset_tsupport (F.test i) hx)

theorem DyadicLipschitzFamily.radius_antitone {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i j : ι) (hij : F.level i ≤ F.level j) :
    F.radius j ≤ F.radius i := by
  rw [F.scale_eq i j hij]
  exact mul_le_of_le_one_right (F.radius_pos i).le
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1))

theorem DyadicLipschitzFamily.radius_eq_of_level_eq {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ}
    (F : DyadicLipschitzFamily ι n d μ c J A) (i j : ι) (hij : F.level i = F.level j) :
    F.radius i = F.radius j := by
  simpa only [hij, Nat.sub_self, pow_zero, mul_one] using! (F.scale_eq i j hij.le).symm

theorem DyadicLipschitzFamily.fine_gram {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (hJ : 0 < J) (hA : 0 ≤ A) (i j : ι) :
    |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      (G * J ^ (n + 1) * A ^ 2) * (F.radius j / F.radius i) * (F.weight j ^ 2 / F.weight i) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact normalized_gram_fine_weighted n G μ hg (F.test i) (F.test j)
    (F.memLp_integrable i).1 (F.memLp_integrable j).1 (F.memLp_integrable j).2 (F.mean_zero j)
    (F.lip i) (F.lipschitz i) (F.center j) (F.radius i) (F.radius j) (F.weight i) (F.weight j)
    J A (F.radius_pos i) (F.radius_pos j) (F.weight_pos i) (F.weight_pos j) hJ hA (F.weight_sq j)
    (F.lip_bound i) (F.value_bound j) (F.support_ball j)

theorem DyadicLipschitzFamily.coarse_gram {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (G : ℝ) (hg : GlobalUpperGrowth n G μ) (hJ : 0 < J) (hA : 0 ≤ A) (i j : ι) :
    |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      (G * J ^ (n + 1) * A ^ 2) * (F.radius i / F.radius j) * F.weight i := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact normalized_gram_coarse_weighted n G μ hg (F.test i) (F.test j)
    (F.memLp_integrable i).1 (F.memLp_integrable j).1 (F.memLp_integrable i).2 (F.mean_zero i)
    (F.lip j) (F.lipschitz j) (F.center i) (F.radius i) (F.radius j) (F.weight i) (F.weight j)
    J A (F.radius_pos i) (F.radius_pos j) (F.weight_pos i) (F.weight_pos j) hJ hA (F.weight_sq i)
    (F.lip_bound j) (F.value_bound i) (F.support_ball i)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ADGramSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicLipschitzFamily.fine_slice_bound {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (i : ι) (t : Finset ι) (k : ℕ)
    (hlevel : ∀ j ∈ t, F.level j = F.level i + k)
    (hnonzero : ∀ j ∈ t, (∫ x, F.test i x * F.test j x ∂μ) ≠ 0) :
    ∑ j ∈ t, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      ((G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        F.weight i * (1 / 2 : ℝ) ^ k := by
  have hlev (j : ι) (hj : j ∈ t) : F.level i ≤ F.level j := by rw [hlevel j hj]; omega
  have hmass := finite_AD_fine_interaction_mass n C G hC μ hg hlower t F.center F.radius c J hc hJ
    (fun j _ => F.center_mem j) (fun j _ => F.radius_pos j) (fun j _ => F.core_admissible j)
    (F.center i) (F.radius i) (F.radius_pos i) (fun j hj => F.radius_antitone i j (hlev j hj))
    (fun j hj => by
      have h := nonzero_gram_centers_near μ (F.test i) (F.test j) (F.center i) (F.center j)
        (J * F.radius i) (J * F.radius j) (F.support_ball i) (F.support_ball j) (hnonzero j hj)
      simpa only [dist_comm] using! h.le)
    (fun j hj l hl hne => F.separated j l (by rw [hlevel j hj, hlevel l hl]) hne)
  have hratio (j : ι) (hj : j ∈ t) : F.radius j / F.radius i = (1 / 2 : ℝ) ^ k := by
    rw [F.scale_eq i j (hlev j hj), hlevel j hj, Nat.add_sub_cancel_left]
    field_simp [(F.radius_pos i).ne']
  let P := G * J ^ (n + 1) * A ^ 2
  have hP : 0 ≤ P := by dsimp [P]; have hG := hg.1; positivity
  calc
    _ ≤ ∑ j ∈ t, P * (1 / 2 : ℝ) ^ k * (F.weight j ^ 2 / F.weight i) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := F.fine_gram G hg hJ hA i j
      rw [hratio j hj] at h
      exact h
    _ = (P * (1 / 2 : ℝ) ^ k / F.weight i) * ∑ j ∈ t, F.radius j ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [F.weight_sq j]
      ring
    _ ≤ (P * (1 / 2 : ℝ) ^ k / F.weight i) *
        (interactionPackingConstant n C G c J * F.radius i ^ n) :=
      mul_le_mul_of_nonneg_left hmass (by have hwi := F.weight_pos i; positivity)
    _ = _ := by
      rw [← F.weight_sq i]
      dsimp only [P]
      field_simp [(F.weight_pos i).ne']

theorem DyadicLipschitzFamily.coarse_slice_bound {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (i : ι) (t : Finset ι) (k : ℕ)
    (hlevel : ∀ j ∈ t, F.level j + k = F.level i)
    (hnonzero : ∀ j ∈ t, (∫ x, F.test i x * F.test j x ∂μ) ≠ 0) :
    ∑ j ∈ t, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      ((G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        F.weight i * (1 / 2 : ℝ) ^ k := by
  classical
  have hP : 0 ≤ G * J ^ (n + 1) * A ^ 2 := by have hG := hg.1; positivity
  have hB : 0 ≤ interactionPackingConstant n C G c J := by
    dsimp [interactionPackingConstant]
    have hG := hg.1
    positivity
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp only [Finset.sum_empty]
    have hwi := F.weight_pos i
    positivity
  obtain ⟨j₀, hj₀⟩ := ht
  have hlev (j : ι) (hj : j ∈ t) : F.level j ≤ F.level i := by have h := hlevel j hj; omega
  have heq (j : ι) (hj : j ∈ t) : F.radius j = F.radius j₀ :=
    F.radius_eq_of_level_eq j j₀ (by have h1 := hlevel j hj; have h2 := hlevel j₀ hj₀; omega)
  have hnear : ∀ j ∈ t, dist (F.center j) (F.center i) ≤ J * F.radius i + J * F.radius j₀ := by
    intro j hj
    have h := nonzero_gram_centers_near μ (F.test i) (F.test j) (F.center i) (F.center j)
      (J * F.radius i) (J * F.radius j) (F.support_ball i) (F.support_ball j) (hnonzero j hj)
    rw [heq j hj] at h
    simpa only [dist_comm] using! h.le
  have hcard := finite_AD_coarse_interaction_card n C G hC μ hg hlower t F.center (F.radius j₀)
    c J (F.radius_pos j₀) hc hJ (fun j _ => F.center_mem j) (F.core_admissible j₀)
    (F.center i) (F.radius i) (F.radius_antitone j₀ i (hlev j₀ hj₀)) hnear (by
      intro j hj l hl hne
      have h := F.separated j l (by have h1 := hlevel j hj; have h2 := hlevel l hl; omega) hne
      simpa only [heq j hj, heq l hl] using! h)
  have hratio (j : ι) (hj : j ∈ t) : F.radius i / F.radius j = (1 / 2 : ℝ) ^ k := by
    have hsub : F.level i - F.level j = k := by have h := hlevel j hj; omega
    rw [F.scale_eq j i (hlev j hj), hsub]
    field_simp [(F.radius_pos j).ne']
  calc
    _ ≤ ∑ _j ∈ t, (G * J ^ (n + 1) * A ^ 2) * (1 / 2 : ℝ) ^ k * F.weight i := by
      apply Finset.sum_le_sum
      intro j hj
      have h := F.coarse_gram G hg hJ hA i j
      rw [hratio j hj] at h
      exact h
    _ = (t.card : ℝ) * ((G * J ^ (n + 1) * A ^ 2) * (1 / 2 : ℝ) ^ k * F.weight i) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ interactionPackingConstant n C G c J *
        ((G * J ^ (n + 1) * A ^ 2) * (1 / 2 : ℝ) ^ k * F.weight i) :=
      mul_le_mul_of_nonneg_right hcard (by have hwi := F.weight_pos i; positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_ADHoleDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
AD lower bounds and global upper growth quantify the density lost to a ball-shaped hole.
Persistent holes at vanishing scales force a measurable set to have zero measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem ballHoleDensityDefect_pos (n : ℕ) (C G : ℝ) (hC : 0 < C) (hG : 0 < G) :
    0 < ballHoleDensityDefect n C G := by
  unfold ballHoleDensityDefect
  positivity

theorem ad_ball_hole_density_bound {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (x z : Ambient d) (r : ℝ) (hr : 0 < r)
    (hz : z ∈ μ.support) (hnear : dist x z ≤ r) (hcore : AdmissibleRadius μ (r / 4))
    (hhole : Disjoint A (ball z (r / 4))) :
    0 < μ.real (closedBall x (2 * r)) ∧
      μ.real (A ∩ closedBall x (2 * r)) / μ.real (closedBall x (2 * r)) ≤
        1 - ballHoleDensityDefect n C G := by
  have hsub : ball z (r / 4) ⊆ closedBall x (2 * r) := by
    intro y hy
    change dist y x ≤ 2 * r
    have ht := dist_triangle y z x
    rw [dist_comm z x] at ht
    change dist y z < r / 4 at hy
    linarith
  have hbig : μ (closedBall x (2 * r)) ≤ ENNReal.ofReal (G * (3 * r) ^ n) :=
    (measure_mono (closedBall_subset_ball (by linarith : 2 * r < 3 * r))).trans
      (hg.2 x (3 * r) (by positivity))
  have hfin : μ (closedBall x (2 * r)) ≠ ∞ := (hbig.trans_lt ENNReal.ofReal_lt_top).ne
  have hholefin := measure_ne_top_of_subset hsub hfin
  have hsmall : (r / 4) ^ n / C ≤ μ.real (ball z (r / 4)) := by
    have h := ENNReal.toReal_mono hholefin (hlower z hz (r / 4) hcore)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C), Measure.real] using! h
  have hpos : 0 < μ.real (closedBall x (2 * r)) :=
    (by positivity : 0 < (r / 4) ^ n / C).trans_le
      (hsmall.trans (measureReal_mono hsub hfin))
  refine ⟨hpos, ?_⟩
  have hsum : μ.real (A ∩ closedBall x (2 * r)) + μ.real (ball z (r / 4)) ≤
      μ.real (closedBall x (2 * r)) := by
    rw [← measureReal_union (hhole.mono_left inter_subset_left) measurableSet_ball
      (measure_ne_top_of_subset inter_subset_right hfin) hholefin]
    exact measureReal_mono (union_subset inter_subset_right hsub) hfin
  have hupper : μ.real (closedBall x (2 * r)) ≤ G * (3 * r) ^ n :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hbig
  have hidentity : ballHoleDensityDefect n C G * (G * (3 * r) ^ n) = (r / 4) ^ n / C := by
    unfold ballHoleDensityDefect
    simp only [mul_pow, div_pow]
    field_simp
  have hdef : ballHoleDensityDefect n C G * μ.real (closedBall x (2 * r)) ≤
      μ.real (ball z (r / 4)) := by
    calc
      _ ≤ ballHoleDensityDefect n C G * (G * (3 * r) ^ n) :=
        mul_le_mul_of_nonneg_left hupper (ballHoleDensityDefect_pos n C G hC hG).le
      _ = _ := hidentity
      _ ≤ _ := hsmall
  apply (div_le_iff₀ hpos).mpr
  linarith

theorem measurable_set_null_of_uniform_ball_holes {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (A : Set (Ambient d)) (hA : MeasurableSet A)
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k) (ht : Tendsto r atTop (𝓝 0))
    (hcore : ∀ k, AdmissibleRadius μ (r k / 4))
    (hhole : ∀ x ∈ A, ∀ k, ∃ z ∈ μ.support, dist x z ≤ r k ∧ Disjoint A (ball z (r k / 4))) :
    μ A = 0 := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hrt : Tendsto (fun k => 2 * r k) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun k => ?_)⟩
    · simpa only [mul_zero] using! ht.const_mul 2
    · change 0 < 2 * r k
      exact mul_pos (by norm_num) (hr k)
  have hzero : ∀ᵐ x ∂μ.restrict A, False := by
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ A, ae_restrict_mem hA] with x hx hxA
    have hd := hx.comp hrt
    have hdreal : Tendsto (fun k => μ.real (A ∩ closedBall x (2 * r k)) /
        μ.real (closedBall x (2 * r k))) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one, Measure.real] using!
        (ENNReal.continuousAt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).tendsto.comp hd
    have hb : (1 : ℝ) ≤ 1 - ballHoleDensityDefect n C G := by
      apply le_of_tendsto hdreal
      apply Filter.Eventually.of_forall
      intro k
      obtain ⟨z, hz, hnear, hh⟩ := hhole x hxA k
      exact (ad_ball_hole_density_bound μ C G hC hG hg hlower A x z (r k) (hr k)
        hz hnear (hcore k) hh).2
    have hp := ballHoleDensityDefect_pos n C G hC hG
    linarith
  simpa using! (ae_iff.mp hzero)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SeparatedSupportNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Maximal separated extensions give covering nets. Positive separation also gives discreteness,
countability in separable spaces, and finiteness on compact sets.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set TopologicalSpace

theorem separated_set_countable {X : Type*} [MetricSpace X] [SeparableSpace X]
    (N : Set X) (r : ℝ) (hr : 0 < r)
    (hsep : N.Pairwise fun x y => r ≤ dist x y) : N.Countable := by
  have hd : N.PairwiseDisjoint (fun x => ball x (r / 2)) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    linarith [hsep hx hy hxy]
  exact hd.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (by positivity)⟩)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_NetDescendantCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netDescendants_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : netDescendants N k z ⊆ E := by
  rintro x ⟨t, hx, _, _⟩
  exact hx

theorem closedNetCell_isClosed {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : IsClosed (closedNetCell N k z) :=
  isClosed_closure

theorem closedNetCell_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hE : IsClosed E) (k : ℕ) (z : E) :
    closedNetCell N k z ⊆ E :=
  hE.closure_subset_iff.mpr (netDescendants_subset N k z)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_ConstructedSupportCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem supportLatticeNets_countable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) : (supportLatticeNets μ R hR k).points.Countable :=
  separated_set_countable _ _ (latticeRadius_pos R hR k) (supportLatticeNets μ R hR k).separated

theorem supportLatticeCell_closed {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : IsClosed (supportLatticeCell μ R hR k z) :=
  closedNetCell_isClosed _ _ _

theorem supportLatticeCell_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R)
    (k : ℕ) (z : (supportLatticeNets μ R hR k).points) : supportLatticeCell μ R hR k z ⊆ μ.support :=
  closedNetCell_subset _ μ.isClosed_support _ _

theorem supportLatticeCell_measure_bounds {n d : ℕ} (μ : Measure (Ambient d)) (C G : ℝ)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (supportLatticeCell μ R hR k z) ∧
      μ (supportLatticeCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  have hball : μ (μ.support ∩ ball (z : Ambient d) (latticeRadius R k / 8)) =
      μ (ball (z : Ambient d) (latticeRadius R k / 8)) := by
    apply measure_congr
    filter_upwards [μ.support_mem_ae] with x hx
    apply propext
    change (x ∈ μ.support ∧ x ∈ ball (z : Ambient d) (latticeRadius R k / 8)) ↔
      x ∈ ball (z : Ambient d) (latticeRadius R k / 8)
    simp only [hx, true_and]
  constructor
  · calc
      _ ≤ μ (ball (z : Ambient d) (latticeRadius R k / 8)) :=
        hlower z ((supportLatticeNets μ R hR k).subset z.property) _ hcore
      _ = _ := hball.symm
      _ ≤ _ := measure_mono (supportLatticeCell_bounds μ R hR k z).1
  · have hsub : closedBall (z : Ambient d) (2 * latticeRadius R k) ⊆
        ball (z : Ambient d) (3 * latticeRadius R k) :=
      closedBall_subset_ball (by have hp := latticeRadius_pos R hR k; linarith)
    apply (measure_mono ((supportLatticeCell_bounds μ R hR k z).2.trans hsub)).trans
    exact hg.2 z _ (mul_pos (by norm_num) (latticeRadius_pos R hR k))

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_SupportCellOverlaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Null overlaps of support lattice cells

The countable union of intersections of distinct closed cells is measurable and avoids
every deep core ball. Upper growth and lower AD bounds turn these holes into nullity;
when a core radius exceeds the support diameter, separation makes the overlap empty.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeOverlap_measurable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : MeasurableSet (supportLatticeOverlap μ R hR k) := by
  classical
  let : Countable (supportLatticeNets μ R hR k).points :=
    (supportLatticeNets_countable μ R hR k).to_subtype
  apply MeasurableSet.iUnion
  intro z
  apply MeasurableSet.iUnion
  intro w
  split_ifs
  · exact MeasurableSet.empty
  · exact (supportLatticeCell_closed μ R hR k z).measurableSet.inter
      (supportLatticeCell_closed μ R hR k w).measurableSet

theorem supportLatticeOverlap_subset_support {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ)
    (hR : 0 < R) (k : ℕ) : supportLatticeOverlap μ R hR k ⊆ μ.support := by
  intro x hx
  obtain ⟨z, _, _, hz, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
  exact supportLatticeCell_subset_support μ R hR k z hz

theorem supportLatticeOverlap_null_of_admissible_core {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 4)) :
    μ (supportLatticeOverlap μ R hR k) = 0 := by
  apply measurable_set_null_of_uniform_ball_holes μ C G hC hG hg hlower
    (supportLatticeOverlap μ R hR k) (supportLatticeOverlap_measurable μ R hR k)
    (fun q => latticeRadius R (k + q)) (fun q => latticeRadius_pos R hR (k + q))
  · simpa only [latticeRadius_add, mul_zero] using!
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 64)
        (by norm_num : (1 / 64 : ℝ) < 1)).const_mul (latticeRadius R k)
  · intro q
    refine ⟨div_pos (latticeRadius_pos R hR (k + q)) (by norm_num), ?_⟩
    exact (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (latticeRadius_antitone R hR.le (Nat.le_add_right k q)) (by norm_num))).trans hcore.2
  · intro x hx q
    have hxE := supportLatticeOverlap_subset_support μ R hR k hx
    obtain ⟨z, hz, hnear⟩ := (supportLatticeNets μ R hR (k + q)).covers x hxE
    exact ⟨z, (supportLatticeNets μ R hR (k + q)).subset hz, hnear.le,
      supportLatticeOverlap_disjoint_deep_core μ R hR k q ⟨z, hz⟩⟩

theorem supportLatticeOverlap_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) : μ (supportLatticeOverlap μ R hR k) = 0 := by
  by_cases hcore : ENNReal.ofReal (latticeRadius R k / 4) ≤ ediam μ.support
  · exact supportLatticeOverlap_null_of_admissible_core μ C G hC hG hg hlower R hR k
      ⟨div_pos (latticeRadius_pos R hR k) (by norm_num), hcore⟩
  · have hempty : supportLatticeOverlap μ R hR k = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨z, w, hne, _, _⟩ := (mem_supportLatticeOverlap μ R hR k x).mp hx
      have hsep := (supportLatticeNets μ R hR k).separated z.property w.property
        (fun h => hne (Subtype.ext h))
      have hdiam := edist_le_ediam_of_mem
        ((supportLatticeNets μ R hR k).subset z.property)
        ((supportLatticeNets μ R hR k).subset w.property)
      apply hcore
      have hp := latticeRadius_pos R hR k
      have hd : latticeRadius R k / 4 ≤ dist (z : Ambient d) (w : Ambient d) := by linarith
      exact (ENNReal.ofReal_le_ofReal hd).trans (by simpa only [edist_dist] using! hdiam)
    rw [hempty, measure_empty]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Restart_CleanSupportPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cleaning the support lattice partition

Removing the union of all cell overlaps produces nested, disjoint measurable cells that
cover the support outside one exceptional set. Net centers avoid that set, so cleaning
preserves the closed cells as closures. Under the growth bounds, it also preserves cell
mass and gives a unique cell at every scale almost everywhere.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

theorem supportLatticeExceptional_null {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) : μ (supportLatticeExceptional μ R hR) = 0 :=
  measure_iUnion_null (fun k => supportLatticeOverlap_null μ C G hC hG hg hlower R hR k)

theorem cleanSupportCell_measure_eq {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) :
    μ (cleanSupportCell μ R hR k z) = μ (supportLatticeCell μ R hR k z) :=
  measure_sdiff_null (supportLatticeExceptional_null μ C G hC hG hg hlower R hR)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_FiniteSupportRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem cleanSupportCell_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) ≤ μ (cleanSupportCell μ R hR k z) ∧
      μ (cleanSupportCell μ R hR k z) ≤ ENNReal.ofReal (G * (3 * latticeRadius R k) ^ n) := by
  rw [cleanSupportCell_measure_eq μ C G hC hG hg hlower R hR k z]
  exact supportLatticeCell_measure_bounds μ C G hg hlower R hR k hcore z

theorem cleanSupportCell_measure_pos_finite {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ z ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball z r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    0 < μ (cleanSupportCell μ R hR k z) ∧ μ (cleanSupportCell μ R hR k z) < ∞ := by
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  exact ⟨(ENNReal.ofReal_pos.mpr (div_pos (pow_pos hcore.1 n) hC)).trans_le hb.1,
    hb.2.trans_lt ENNReal.ofReal_lt_top⟩

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Foundations_OriginalDyadicTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicOscillationTests.normalized_pairing_sq {ι : Type*} {d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J) (n : ℕ) (hJ : 0 < J)
    (i : ι) (u : Ambient d → ℝ) :
    (∫ x, (F.normalized n hJ).test i x * u x ∂μ) ^ 2 =
      (∫ x, F.test i x * u x ∂μ) ^ 2 / F.radius i ^ n := by
  change (∫ x, ((F.weight n i)⁻¹ * F.test i x) * u x ∂μ) ^ 2 = _
  simp_rw [mul_assoc]
  rw [integral_const_mul, mul_pow, inv_pow, F.weight_sq n i]
  ring

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

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_TruncationIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrability of hard Riesz truncations

Global upper growth makes the Riesz kernel square-integrable outside each positive-radius
ball. Pairing this exterior estimate with an L² input proves integrability of the hard
truncation. For finite measures, integrability instead follows from the bounded exterior
kernel and the inclusion of L² in L¹.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem truncation_integrable_of_finiteMeasure {d : ℕ} (n : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (x : Ambient d) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun y => f y • kernel n x y) {y | ε < dist x y} μ := by
  apply (hf.integrable (by norm_num)).restrict.smul_bdd ((ε ^ n)⁻¹)
    (kernel_measurable_right n x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable)] with y hy
  exact kernel_norm_le_truncation n x y ε hε hy.le

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

theorem scalarTruncatedKernel_measurable {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ) :
    Measurable (scalarTruncatedKernel m e ε) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  unfold scalarTruncatedKernel kernel
  apply Measurable.ite (measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)
  · fun_prop
  · exact measurable_const

theorem scalarTruncatedKernel_bound {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (hε : 0 < ε) (q : Ambient d × Ambient d) :
    |scalarTruncatedKernel m e ε q| ≤ ‖e‖ * (ε ^ m)⁻¹ := by
  unfold scalarTruncatedKernel
  split_ifs with h
  · have hi : |inner ℝ e (kernel m q.1 q.2)| ≤ ‖e‖ * ‖kernel m q.1 q.2‖ := by
      simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) e (kernel m q.1 q.2)
    apply hi.trans
    exact mul_le_mul_of_nonneg_left (kernel_norm_le_truncation m q.1 q.2 ε hε h.le) (norm_nonneg e)
  · simp only [abs_zero]
    positivity

theorem scalarTruncatedKernel_swap {d : ℕ} (m : ℕ) (e : Ambient d) (ε : ℝ)
    (q : Ambient d × Ambient d) :
    scalarTruncatedKernel m e ε q.swap = -scalarTruncatedKernel m e ε q := by
  unfold scalarTruncatedKernel
  dsimp only [Prod.swap]
  simp only [dist_comm q.2 q.1]
  split_ifs
  · rw [kernel_antisymm, inner_neg_right]
  · exact neg_zero.symm

theorem truncated_inner_eq_scalar_integral {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε) (x : Ambient d) :
    inner ℝ e (truncated m ν ε (fun _ => 1) x) =
      ∫ y, scalarTruncatedKernel m e ε (x, y) ∂ν := by
  have hi : IntegrableOn (kernel m x) {y | ε < dist x y} ν := by
    simpa only [one_smul] using! truncation_integrable_of_finiteMeasure m ν (fun _ => 1)
      (memLp_const 1) x ε hε
  unfold truncated
  simp only [one_smul]
  rw [← integral_inner (𝕜 := ℝ) hi e]
  have hs : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  rw [← integral_indicator hs]
  rfl

theorem truncated_weighted_pair_integrable {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν) :
    Integrable (fun q : Ambient d × Ambient d => φ q.1 * scalarTruncatedKernel m e ε q) (ν.prod ν) := by
  have hdom := (hφ.abs.mul_prod (integrable_const (μ := ν) (1 : ℝ))).mul_const (‖e‖ * (ε ^ m)⁻¹)
  apply hdom.mono' ((hφm.comp measurable_fst).mul (scalarTruncatedKernel_measurable m e ε)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul, mul_one]
  exact mul_le_mul_of_nonneg_left (scalarTruncatedKernel_bound m e ε hε q) (abs_nonneg _)

theorem finite_truncated_pairing_symmetrization {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (ε : ℝ) (hε : 0 < ε)
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν) :
    (∫ x, φ x * inner ℝ e (truncated m ν ε (fun _ => 1) x) ∂ν) =
      (1 / 2 : ℝ) * (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        rieszInteriorIntegrand m e φ q ∂ν.prod ν) := by
  let F := fun q : Ambient d × Ambient d => φ q.1 * scalarTruncatedKernel m e ε q
  let G := fun q : Ambient d × Ambient d => scalarTruncatedKernel m e ε q * (φ q.1 - φ q.2)
  have hF : Integrable F (ν.prod ν) := truncated_weighted_pair_integrable m e ν ε hε φ hφm hφ
  have hswap : Integrable (fun q : Ambient d × Ambient d => F q.swap) (ν.prod ν) := hF.swap
  have heq : G = fun q => F q + F q.swap := by
    funext q
    dsimp only [F, G]
    rw [scalarTruncatedKernel_swap]
    dsimp only [Prod.swap]
    ring
  have hG : (∫ q, G q ∂ν.prod ν) = 2 * (∫ q, F q ∂ν.prod ν) := by
    rw [heq, integral_add hF hswap, integral_prod_swap]
    ring
  have hleft : (∫ x, φ x * inner ℝ e (truncated m ν ε (fun _ => 1) x) ∂ν) =
      ∫ q, F q ∂ν.prod ν := by
    calc
      _ = ∫ x, ∫ y, F (x, y) ∂ν ∂ν := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        change φ x * inner ℝ e (truncated m ν ε (fun _ => 1) x) = ∫ y, F (x, y) ∂ν
        rw [truncated_inner_eq_scalar_integral m e ν ε hε x]
        exact (integral_const_mul (φ x) _).symm
      _ = _ := (integral_prod F hF).symm
  have hright : (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
      rieszInteriorIntegrand m e φ q ∂ν.prod ν) = ∫ q, G q ∂ν.prod ν := by
    rw [← integral_indicator (measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    by_cases h : ε < dist q.1 q.2
    · rw [Set.indicator_of_mem (show q ∈ {q : Ambient d × Ambient d | ε < dist q.1 q.2} from h)]
      simp only [G, scalarTruncatedKernel, ite_eq_left h, rieszInteriorIntegrand]
    · rw [Set.indicator_of_notMem (show q ∉ {q : Ambient d × Ambient d | ε < dist q.1 q.2} from h)]
      simp only [G, scalarTruncatedKernel, ite_eq_right h, zero_mul]
  rw [hleft, hright, hG]
  ring

theorem finite_truncated_pairing_tendsto_of_integrable {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (φ : Ambient d → ℝ) (hφm : Measurable φ) (hφ : Integrable φ ν)
    (hpair : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated m ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν)
      atTop (𝓝 ((1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν))) := by
  let s := fun k : ℕ => {q : Ambient d × Ambient d | (1 / 2 : ℝ) ^ k < dist q.1 q.2}
  have hs (k : ℕ) : MeasurableSet (s k) :=
    measurableSet_lt measurable_const (continuous_fst.dist continuous_snd).measurable
  have hmono : Monotone s := by
    intro k l hkl q hq
    exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hkl) hq
  have hcover : Function.support (rieszInteriorIntegrand m e φ) ⊆ ⋃ k, s k := by
    intro q hq
    have hne : q.1 ≠ q.2 := by
      intro heq
      apply hq
      simp only [rieszInteriorIntegrand, heq, kernel_self, inner_zero_right, zero_mul]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne) (by norm_num : (1 / 2 : ℝ) < 1)
    exact mem_iUnion.mpr ⟨k, hk⟩
  have hfull : (∫ q in ⋃ k, s k, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
      ∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro q hq
    by_contra hn
    exact hq (hcover hn)
  have ht := tendsto_setIntegral_of_monotone hs hmono hpair.restrict
  rw [hfull] at ht
  have heq : (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated m ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν) =
      fun k => (1 / 2 : ℝ) * (∫ q in s k, rieszInteriorIntegrand m e φ q ∂ν.prod ν) := by
    funext k
    exact finite_truncated_pairing_symmetrization m e ν _ (by positivity) φ hφm hφ
  rw [heq]
  exact ht.const_mul (1 / 2 : ℝ)

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

theorem finite_localized_pairing_limit {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφLip : LipschitzWith L φ)
    (hφ : Integrable φ ν) (r : ℝ) (hr : 0 < r)
    (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated (p + 1) ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν)
      atTop (𝓝 ((1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q ∂ν.prod ν))) :=
  finite_truncated_pairing_tendsto_of_integrable (p + 1) e ν φ hφLip.continuous.measurable hφ
    (rieszInteriorIntegrand_integrable_of_lipschitz p C ν hg e φ L hφLip r hr hdiam)

theorem truncated_restriction_eq_indicator {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (ε : ℝ) (x : Ambient d) :
    truncated m (μ.restrict s) ε (fun _ => 1) x = truncated m μ ε (s.indicator (fun _ => 1)) x := by
  classical
  have ht : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have heq : (fun y => s.indicator (fun _ => (1 : ℝ)) y • kernel m x y) = s.indicator (kernel m x) := by
    funext y
    by_cases hy : y ∈ s
    · simp only [Set.indicator_of_mem hy, one_smul]
    · simp only [Set.indicator_of_notMem hy, zero_smul]
  unfold truncated
  simp only [one_smul]
  rw [heq, integral_indicator hs, Measure.restrict_restrict ht, Measure.restrict_restrict hs, inter_comm]

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

theorem finite_truncations_tendsto_renormalized {d : ℕ} (p : ℕ) (C : ℝ)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (hg : GlobalUpperGrowth (p + 1) C ν)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφLip : LipschitzWith L φ)
    (hφ : Integrable φ ν) (r : ℝ) (hr : 0 < r)
    (hdiam : ∀ᵐ q ∂ν.prod ν, dist q.1 q.2 ≤ r)
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hφzero : ∀ x ∉ ball a R, φ x = 0) (hzero : (∫ x in ball a R, φ x ∂ν) = 0) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e (truncated (p + 1) ν ((1 / 2 : ℝ) ^ k) (fun _ => 1) x) ∂ν)
      atTop (𝓝 (rieszScalarPairing (p + 1) ν a R e φ)) := by
  have hF := rieszInteriorIntegrand_integrable_of_lipschitz p C ν hg e φ L hφLip r hr hdiam
  have heq := (finite_pairing_eq_renormalized (p + 1) e ν a R hR φ hφ hφzero hzero hF).2
  rw [← heq]
  exact finite_localized_pairing_limit p C ν hg e φ L hφLip hφ r hr hdiam

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_LocalizedRieszPairingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Localized scalar Riesz pairing bounds

Lipschitz cancellation bounds the interior integrand by a weakly singular kernel.
The exterior estimate uses compact support and the normal height to control its
tail, giving quantitative bounds for the localized scalar pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem rieszFarIntegrand_integral_abs_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    (∫ q, |rieszFarIntegrand m e φ a q|
      ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) ≤
      (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * (∫ x in ball a R, |φ x| ∂μ)) * (2 * (C * 2 ^ m / R)) := by
  have hC : 0 ≤ C := hg.1
  let ν := μ.restrict (ball a R)
  let w := affineNormalHeight e a 0
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hw : LipschitzWith ‖e‖₊ w := affineNormalHeight_lipschitz e a 0
  have hwa : w a = 0 := by simp only [w, affineNormalHeight, sub_self, inner_zero_right]
  have hwL2 := lipschitz_height_memLp_on_ball m C μ hg w ‖e‖₊ hw a R hR
  have hφL2 := lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR
  have hφI : Integrable φ ν := hφL2.integrable (by norm_num)
  have hφw : Integrable (fun x => φ x * w x) ν :=
    memLp_one_iff_integrable.mp (MeasureTheory.MemLp.mul (hφ := hφL2) (hf := hwL2))
  have hmoment : (∫ x, |φ x * w x| ∂ν) ≤
      (‖e‖ * H) * (∫ x, |φ x| ∂ν) := by
    calc
      _ ≤ ∫ x, (‖e‖ * H) * |φ x| ∂ν := by
        apply integral_mono hφw.abs (hφI.abs.const_mul _)
        intro x
        change |φ x * w x| ≤ (‖e‖ * H) * |φ x|
        by_cases hx : φ x = 0
        · simp only [hx, zero_mul, abs_zero, mul_zero, le_refl]
        have hwx : |w x| ≤ ‖e‖ * H := by
          have hb := hw.dist_le_mul x a
          simp only [Real.dist_eq, hwa, sub_zero, coe_nnnorm] at hb
          exact hb.trans (mul_le_mul_of_nonneg_left (hsupport x hx) (norm_nonneg _))
        rw [abs_mul, mul_comm (‖e‖ * H)]
        exact mul_le_mul_of_nonneg_left hwx (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  obtain ⟨hweighted, hZ⟩ := weighted_height_closed_tail_bound m C μ hg w ‖e‖₊ hw a R hR
  simp only [hwa, abs_zero, zero_div, add_zero, coe_nnnorm] at hZ
  have hb := (renormalized_far_pairing_integrable_and_bound m C μ ν hg w φ
    hw.continuous.measurable hφ.continuous.measurable hφI hφw a H R hH hR hHR
    (Eventually.of_forall hsupport) hweighted _ hZ).2
  have heq : rieszFarIntegrand m e φ a = renormalizedNormalIntegrand m w φ a := by
    funext q
    rw [rieszFarIntegrand_eq_normal_sub_correction m e w φ
      (affineNormalHeight_difference e a 0), hwa, mul_zero, zero_mul, sub_zero]
  rw [heq]
  calc
    _ ≤ _ := hb
    _ ≤ 2 ^ (m + 1) * (((‖e‖ * H) * (∫ x, |φ x| ∂ν)) *
        (2 * (C * 2 ^ m / R))) +
        ((m + 1 : ℝ) * 2 ^ (m + 2) * H) *
          ((∫ x, |φ x| ∂ν) * (‖e‖ * (2 * (C * 2 ^ m / R)))) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hmoment (by positivity)) (by positivity)
    _ = _ := by dsimp only [ν] <;> ring

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
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OuterCutoffError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem riesz_pairing_outer_cutoff_error_bound {d : ℕ} (m : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m G μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (z a : Ambient d) (H R T : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hcontain : ball z R ⊆ ball a T)
    (hsupport : ∀ x, φ x ≠ 0 → dist x z ≤ H) :
    |rieszScalarPairing m μ z R e φ -
      rieszScalarPairing m (μ.restrict (ball a T)) z R e φ| ≤
      (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) *
        (‖e‖ * H * (∫ x in ball z R, |φ x| ∂μ)) * (2 * (G * 2 ^ m / R)) := by
  have hi := rieszFarIntegrand_integrable_of_compact_lipschitz m G μ hg e φ L hφ
    z H R hH hR hHR hsupport
  have hb := rieszFarIntegrand_integral_abs_bound m G μ hg e φ L hφ z H R
    hH hR hHR hsupport
  rw [rieszScalarPairing_restrict_outer_ball m μ z a R T hcontain e φ]
  unfold rieszScalarPairing
  dsimp only
  rw [add_sub_add_left_eq_sub]
  rw [← setIntegral_compl (MeasurableSet.univ.prod measurableSet_ball) hi]
  calc
    _ ≤ ∫ q in (univ ×ˢ ball a T)ᶜ, |rieszFarIntegrand m e φ z q|
        ∂(μ.restrict (ball z R)).prod (μ.restrict (closedExterior z R)) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ q, |rieszFarIntegrand m e φ z q|
        ∂(μ.restrict (ball z R)).prod (μ.restrict (closedExterior z R)) :=
      integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun q => abs_nonneg _) hi.abs
    _ ≤ _ := hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Kernel_OriginalTestCutoffError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Outer-cutoff errors for mean-zero Lipschitz tests

Restricting the measure to a large ball changes a scalar Riesz pairing by a
controlled tail. The explicit oscillation constant combines the compact test's
amplitude bound with growth and cancellation estimates outside that ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem oscillationTailConstant_nonneg (n : ℕ) (G J : ℝ) (hG : 0 ≤ G) (hJ : 0 ≤ J) :
    0 ≤ oscillationTailConstant n G J := by
  unfold oscillationTailConstant
  positivity

theorem original_test_outer_cutoff_error {d : ℕ} [Nontrivial (Ambient d)]
    (p : ℕ) (G : ℝ) (μ : Measure (Ambient d)) [SFinite μ]
    (hg : GlobalUpperGrowth (p + 1) G μ)
    (e : Ambient d) (he : ‖e‖ ≤ 1) (φ : Ambient d → ℝ) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (z a : Ambient d) (r J R T : ℝ)
    (hr : 0 < r) (hJ : 0 < J) (hR : 0 < R) (hsmall : 2 * (J * r) ≤ R)
    (hcontain : ball z R ⊆ ball a T)
    (hL : (L : ℝ) ≤ 1 / r) (hsupport : tsupport φ ⊆ ball z (J * r))
    (hzero : (∫ x, φ x ∂μ) = 0) :
    |rieszScalarPairing (p + 1) μ z (2 * (J * r)) e φ -
      rieszScalarPairing (p + 1) (μ.restrict (ball a T)) z (2 * (J * r)) e φ| ≤
      oscillationTailConstant (p + 1) G J * (r / R) * r ^ (p + 1) := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hJr : 0 < J * r := mul_pos hJ hr
  have hs : ∀ x, φ x ≠ 0 → dist x z ≤ J * r :=
    fun x hx => (hsupport (subset_tsupport φ hx)).le
  have houter : ∀ x ∉ ball a T, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx (hcontain ((ball_subset_ball (by linarith)) (hsupport (subset_tsupport φ hn))))
  have hzeroν : (∫ x, φ x ∂μ.restrict (ball a T)) = 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero houter).trans hzero
  have heqμ := rieszScalarPairing_localization_independent p G μ hg e φ L hφ z z
    (J * r) (J * r) (2 * (J * r)) R hJr.le hJr.le (by positivity) hR le_rfl hsmall hs hs hzero
  have heqν := rieszScalarPairing_localization_independent p G (μ.restrict (ball a T))
    (globalGrowth_restrict (p + 1) G μ hg (ball a T)) e φ L hφ z z
    (J * r) (J * r) (2 * (J * r)) R hJr.le hJr.le (by positivity) hR le_rfl hsmall hs hs hzeroν
  rw [heqμ, heqν]
  have hI := (compact_lipschitz_test_memLp μ φ L hφ z (J * r) hsupport).2
  have hval := original_oscillation_test_amplitude φ L hφ z r J hr hJ hL hsupport
  have hmass : μ.real (ball z (J * r)) ≤ G * (J * r) ^ (p + 1) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg hJr.le _)) (hg.2 z _ hJr)
  have hL1 : (∫ x in ball z R, |φ x| ∂μ) ≤ (2 * J) * (G * (J * r) ^ (p + 1)) := by
    calc
      _ ≤ ∫ x, |φ x| ∂μ := integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun x => abs_nonneg _) hI.abs
      _ ≤ (2 * J) * μ.real (ball z (J * r)) :=
        integral_abs_le_support_ball_mass μ φ hI z (J * r) (2 * J) hval
          (fun x hx => hsupport (subset_tsupport φ hx))
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  calc
    _ ≤ _ := riesz_pairing_outer_cutoff_error_bound (p + 1) G μ hg e φ L hφ z a
      (J * r) R T hJr.le hR hsmall hcontain hs
    _ ≤ (2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) *
        (1 * (J * r) * ((2 * J) * (G * (J * r) ^ (p + 1)))) * (2 * (G * 2 ^ (p + 1) / R)) := by
      have hG := hg.1
      simp only [Nat.cast_add, Nat.cast_one]
      gcongr
    _ = _ := by
      unfold oscillationTailConstant
      simp only [Nat.cast_add, Nat.cast_one]
      rw [mul_pow]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Limits_FixedCutoffPairingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fixed-cutoff limits of hard-truncated pairings

Restricting a globally growing measure to the outer ball gives a finite measure.
Mean-zero Lipschitz tests then identify the limit of dyadic hard truncations
with the scalar Riesz pairing on that restriction. The ball indicator also has
finite squared integral equal to the real mass of the ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem fixed_cutoff_hard_pairing_limit {d : ℕ} (p : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) G μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (z : Ambient d) (R : ℝ) (hR : 0 < R)
    (houter : ∀ x ∉ ball a T, φ x = 0)
    (hinner : ∀ x ∉ ball z R, φ x = 0)
    (hzero : (∫ x, φ x ∂μ) = 0) :
    Tendsto (fun k : ℕ => ∫ x, φ x * inner ℝ e
      (truncated (p + 1) μ ((1 / 2 : ℝ) ^ k) ((ball a T).indicator (fun _ => 1)) x) ∂μ)
      atTop (𝓝 (rieszScalarPairing (p + 1) (μ.restrict (ball a T)) z R e φ)) := by
  let ν := μ.restrict (ball a T)
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) G μ hg a T hT
  have hφI : Integrable φ ν :=
    (lipschitz_height_memLp_on_ball (p + 1) G μ hg φ L hφ a T hT).integrable (by norm_num)
  have hzeroν : (∫ x in ball z R, φ x ∂ν) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hinner]
    change (∫ x in ball a T, φ x ∂μ) = 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero houter, hzero]
  have ht := finite_truncations_tendsto_renormalized p G ν
    (globalGrowth_restrict (p + 1) G μ hg (ball a T)) e φ L hφ hφI
    (2 * T) (by positivity) (ball_restriction_pair_diameter μ a T)
    z R hR hinner hzeroν
  have heq (ε : ℝ) : (∫ x, φ x * inner ℝ e (truncated (p + 1) ν ε (fun _ => 1) x) ∂ν) =
      ∫ x, φ x * inner ℝ e
        (truncated (p + 1) μ ε ((ball a T).indicator (fun _ => 1)) x) ∂μ := by
    dsimp only [ν]
    simp_rw [truncated_restriction_eq_indicator (p + 1) μ (ball a T) measurableSet_ball]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [houter x hx, zero_mul]
  simpa only [heq] using! ht

theorem ball_indicator_one_memLp_and_sq_integral {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T) :
    MemLp ((ball a T).indicator (fun _ => (1 : ℝ))) 2 μ ∧
      (∫ x, ((ball a T).indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂μ) = μ.real (ball a T) := by
  let : IsFiniteMeasure (μ.restrict (ball a T)) :=
    finiteMeasure_restrict_ball_of_globalGrowth n G μ hg a T hT
  refine ⟨(memLp_indicator_iff_restrict measurableSet_ball).mpr (memLp_const (1 : ℝ)), ?_⟩
  have heq : (fun x => ((ball a T).indicator (fun _ => (1 : ℝ)) x) ^ 2) =
      (ball a T).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ ball a T <;> simp only [indicator_of_mem, indicator_of_notMem, hx,
      not_false_eq_true, one_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [heq, integral_indicator measurableSet_ball, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_LatticeMassPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mass bounds for lattice descendants

Each descendant cell is contained in a ball with controlled radius. Global
upper growth therefore bounds its mass by a constant times the corresponding
power of its radius, both in extended and real-valued form.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem SupportCellDescendant.measure_upper {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ i.cell ≤ ENNReal.ofReal (G * (3 * i.radius) ^ n) := by
  have hr := i.radius_pos
  have hs := (supportLatticeCell_bounds μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).2
  have hb : closedBall i.center (2 * i.radius) ⊆ ball i.center (3 * i.radius) :=
    closedBall_subset_ball (by linarith [i.radius_pos])
  exact (measure_mono ((sdiff_subset.trans hs).trans hb)).trans
    (hg.2 i.center (3 * i.radius) (by positivity))

theorem SupportCellDescendant.real_measure_upper {n d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z) (G : ℝ) (hg : GlobalUpperGrowth n G μ) :
    μ.real i.cell ≤ (G * 3 ^ n) * i.radius ^ n := by
  have hG := hg.1
  have hr := i.radius_pos
  have hb := ENNReal.toReal_le_of_le_ofReal
    (by positivity : 0 ≤ G * (3 * i.radius) ^ n) (i.measure_upper G hg)
  simpa only [mul_pow, mul_assoc, Measure.real] using! hb

theorem cleanSupportCell_real_measure_bounds {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) :
    (latticeRadius R k / 8) ^ n / C ≤ μ.real (cleanSupportCell μ R hR k z) ∧
      μ.real (cleanSupportCell μ R hR k z) ≤ (G * 3 ^ n) * latticeRadius R k ^ n := by
  have hr := latticeRadius_pos R hR k
  have hb := cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z
  have hf : μ (cleanSupportCell μ R hR k z) ≠ ∞ := (hb.2.trans_lt ENNReal.ofReal_lt_top).ne
  constructor
  · simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (latticeRadius R k / 8) ^ n / C),
      Measure.real] using! ENNReal.toReal_mono hf hb.1
  · have hu := ENNReal.toReal_le_of_le_ofReal
      (by positivity : 0 ≤ G * (3 * latticeRadius R k) ^ n) hb.2
    simpa only [mul_pow, mul_assoc, Measure.real] using! hu

theorem latticeMassPackingConstant_pos (n : ℕ) (C G B : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hB : 0 < B) : 0 < latticeMassPackingConstant n C G B := by
  unfold latticeMassPackingConstant
  positivity

theorem cell_mass_packing_of_radius_packing {ι : Type*} {n d : ℕ}
    (μ : Measure (Ambient d)) (C G B : ℝ) (hC : 0 < C) (hG : 0 < G) (hB : 0 ≤ B)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (f : ι → SupportCellDescendant μ R hR k z) (s : Finset ι)
    (hpack : ∑ i ∈ s, (f i).radius ^ n ≤ B * (2 * latticeRadius R k) ^ n) :
    ∑ i ∈ s, μ.real (f i).cell ≤
      latticeMassPackingConstant n C G B * μ.real (cleanSupportCell μ R hR k z) := by
  have hl := (cleanSupportCell_real_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have hK : 0 ≤ latticeMassPackingConstant n C G B := by
    unfold latticeMassPackingConstant
    positivity
  have hid : (G * 3 ^ n) * (B * (2 * latticeRadius R k) ^ n) =
      latticeMassPackingConstant n C G B * ((latticeRadius R k / 8) ^ n / C) := by
    unfold latticeMassPackingConstant
    simp only [mul_pow, div_pow]
    field_simp
  calc
    _ ≤ ∑ i ∈ s, (G * 3 ^ n) * (f i).radius ^ n :=
      Finset.sum_le_sum (fun i _ => (f i).real_measure_upper G hg)
    _ = (G * 3 ^ n) * ∑ i ∈ s, (f i).radius ^ n := (Finset.mul_sum ..).symm
    _ ≤ (G * 3 ^ n) * (B * (2 * latticeRadius R k) ^ n) :=
      mul_le_mul_of_nonneg_left hpack (by positivity)
    _ = _ := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hK

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_CoarseLevelPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem finite_sum_of_bounded_level_slices {ι : Type*}
    (s : Finset ι) (level : ι → ℕ) (mass : ι → ℝ) (N : ℕ) (B : ℝ)
    (hlevel : ∀ i ∈ s, level i < N)
    (hslice : ∀ k < N, ∑ i ∈ s with level i = k, mass i ≤ B) :
    ∑ i ∈ s, mass i ≤ (N : ℝ) * B := by
  classical
  have hsum : (∑ k ∈ Finset.range N, ∑ i ∈ s with level i = k, mass i) = ∑ i ∈ s, mass i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_range.mpr (hlevel i hi)) mass
  rw [← hsum]
  calc
    _ ≤ ∑ _k ∈ Finset.range N, B := Finset.sum_le_sum (fun k hk => hslice k (Finset.mem_range.mp hk))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem DyadicOscillationTests.coarse_level_packing {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J : ℝ} (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (s : Finset ι) (N : ℕ) (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hcenters : ∀ i ∈ s, dist (F.center i) a ≤ R)
    (hradii : ∀ i ∈ s, F.radius i ≤ R) :
    ∑ i ∈ s with F.level i < N, F.radius i ^ n ≤
      ((N : ℝ) * ((C / c ^ n) * G * (1 + c) ^ n)) * R ^ n := by
  classical
  let t := s.filter (fun i => F.level i < N)
  have hb := finite_sum_of_bounded_level_slices t F.level (fun i => F.radius i ^ n) N
    (((C / c ^ n) * G * (1 + c) ^ n) * R ^ n)
    (fun i hi => (Finset.mem_filter.mp hi).2) (by
      intro k _
      let q := t.filter (fun i => F.level i = k)
      have hqs (i : ι) (hi : i ∈ q) : i ∈ s :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      have hbound := finite_AD_core_mass_packing n C G hC μ hg hlower q F.center F.radius c hc
        (fun i _ => F.center_mem i) (fun i _ => F.radius_pos i) (fun i _ => F.core_admissible i)
        a ((1 + c) * R) (by positivity)
        (by
          intro i hi
          have hcR := mul_le_mul_of_nonneg_left (hradii i (hqs i hi)) hc.le
          linarith [hcenters i (hqs i hi)])
        (by
          intro i hi j hj hij
          exact F.separated i j ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij)
      simpa only [mul_pow, mul_assoc] using! hbound)
  simpa only [mul_assoc] using! hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_ADTestFamilyBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bessel estimate for dyadic Lipschitz test families

Summable bounds on the scale slices of the Gram matrix give a Bessel inequality
for finite families of test functions under upper growth and lower AD bounds.
The resulting constant depends explicitly on the interaction packing estimate.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicLipschitzFamily.bessel {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (s : Finset ι)
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, F.test i x * u x ∂μ) ^ 2 ≤
      (4 * (G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, u x ^ 2 ∂μ := by
  classical
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let P := G * J ^ (n + 1) * A ^ 2
  let B := interactionPackingConstant n C G c J
  have hP : 0 ≤ P := by dsimp [P]; have hG := hg.1; positivity
  have hB : 0 ≤ B := by dsimp [B, interactionPackingConstant]; have hG := hg.1; positivity
  have hslice : ∀ i ∈ s, ∀ k : ℕ,
      ∑ j ∈ s with Nat.dist (F.level i) (F.level j) = k,
        |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
        (2 * P * B) * F.weight i * (1 / 2 : ℝ) ^ k := by
    intro i _ k
    let q := s.filter (fun j => Nat.dist (F.level i) (F.level j) = k)
    let t := q.filter (fun j => (∫ x, F.test i x * F.test j x ∂μ) ≠ 0)
    have hdrop : (∑ j ∈ q, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j) =
        ∑ j ∈ t, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      have hz : (∫ x, F.test i x * F.test j x ∂μ) = 0 := by
        by_contra hn
        exact hnot (Finset.mem_filter.mpr ⟨hj, hn⟩)
      simp only [hz, abs_zero, zero_mul]
    have hnonzero (j : ι) (hj : j ∈ t) : (∫ x, F.test i x * F.test j x ∂μ) ≠ 0 :=
      (Finset.mem_filter.mp hj).2
    have hgap (j : ι) (hj : j ∈ t) : Nat.dist (F.level i) (F.level j) = k :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    have hf := F.fine_slice_bound C G hC hg hlower hc hJ hA i
      (t.filter (fun j => F.level i ≤ F.level j)) k (by
        intro j hj
        obtain ⟨hjt, hle⟩ := Finset.mem_filter.mp hj
        have h := hgap j hjt
        rw [Nat.dist_eq_sub_of_le hle] at h
        omega) (fun j hj => hnonzero j (Finset.mem_filter.mp hj).1)
    have hco := F.coarse_slice_bound C G hC hg hlower hc hJ hA i
      (t.filter (fun j => ¬ F.level i ≤ F.level j)) k (by
        intro j hj
        obtain ⟨hjt, hlt⟩ := Finset.mem_filter.mp hj
        have h := hgap j hjt
        rw [Nat.dist_eq_sub_of_le_right (by omega)] at h
        omega) (fun j hj => hnonzero j (Finset.mem_filter.mp hj).1)
    change (∑ j ∈ q, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j) ≤ _
    rw [hdrop, ← Finset.sum_filter_add_sum_filter_not t (fun j => F.level i ≤ F.level j)]
    have h := add_le_add hf hco
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [P, B]
    ring
  have hb := finite_L2_bessel_of_geometric_gram_slices μ s F.test (fun i => (F.memLp_integrable i).1)
    F.weight (fun i j => Nat.dist (F.level i) (F.level j)) (2 * P * B) (by positivity)
    (fun i _ => F.weight_pos i) hslice u hu
  convert! hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [P, B]
  ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_VectorBesselTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transferring scalar Bessel bounds to vector fields

Scalar-vector pairings commute with the Bochner integral, and the squared native
`L²` norm agrees with the integral of the squared pointwise norm. Expanding in an
orthonormal basis transfers a finite scalar Bessel bound to pairings of a vector
field against test vectors of norm at most one, with the same Bessel constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem memLp_inner_const_of_vector {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (u : X → E) (hu : MemLp u 2 μ) (e : E) :
    MemLp (fun x => inner ℝ e (u x)) 2 μ :=
  hu.of_le_mul (aestronglyMeasurable_const.inner hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm (𝕜 := ℝ) e (u x))

theorem integral_scalar_vector_pairing {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (f : X → ℝ) (u : X → E)
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (e : E) :
    (∫ x, f x * inner ℝ e (u x) ∂μ) = inner ℝ e (∫ x, f x • u x ∂μ) := by
  have hi : Integrable (fun x => f x • u x) μ := memLp_one_iff_integrable.mp (MemLp.smul (hf := hu) (hφ := hf))
  simpa only [real_inner_smul_right] using! (integral_inner (𝕜 := ℝ) hi e)

theorem toLp_vector_norm_sq_eq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (u : X → E) (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem vector_sq_integral_of_native_norm_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure X) (f : X → ℝ) (u : X → E)
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) (D : ℝ≥0)
    (hN : eLpNorm u 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ (D : ℝ) ^ 2 * ∫ x, f x ^ 2 ∂μ := by
  have hfin : (D : ℝ≥0∞) * eLpNorm f 2 μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hf.eLpNorm_ne_top
  have hnorm : ‖hu.toLp u‖ ≤ (D : ℝ) * ‖hf.toLp f‖ := by
    simpa only [Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.coe_toReal] using!
      ENNReal.toReal_mono hfin hN
  rw [← toLp_vector_norm_sq_eq_integral μ u hu, ← toLp_norm_sq_eq_integral μ f hf]
  have hh := mul_self_le_mul_self (norm_nonneg (hu.toLp u)) hnorm
  nlinarith

theorem finite_vector_bessel_of_scalar {ι κ X E : Type*} [Fintype κ]
    [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis κ ℝ E) (μ : Measure X) (s : Finset ι)
    (f : ι → X → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (B : ℝ)
    (hb : ∀ v : X → ℝ, MemLp v 2 μ →
      ∑ i ∈ s, (∫ x, f i x * v x ∂μ) ^ 2 ≤ B * ∫ x, v x ^ 2 ∂μ)
    (u : X → E) (hu : MemLp u 2 μ) (e : ι → E)
    (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, f i x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤
      B * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  classical
  let v : ι → E := fun i => ∫ x, f i x • u x ∂μ
  have hv (i : ι) (hi : i ∈ s) :
      (∫ x, f i x * inner ℝ (e i) (u x) ∂μ) ^ 2 ≤ ‖v i‖ ^ 2 := by
    rw [integral_scalar_vector_pairing μ (f i) u (hf i) hu (e i)]
    have hnorm : |inner ℝ (e i) (v i)| ≤ ‖v i‖ := by
      calc
        _ ≤ ‖e i‖ * ‖v i‖ := by
          simpa only [Real.norm_eq_abs] using! norm_inner_le_norm (𝕜 := ℝ) (e i) (v i)
        _ ≤ 1 * ‖v i‖ := mul_le_mul_of_nonneg_right (he i hi) (norm_nonneg _)
        _ = _ := one_mul _
    have hh := mul_self_le_mul_self (abs_nonneg _) hnorm
    simpa only [← pow_two, sq_abs] using! hh
  have hcoord (k : κ) := memLp_inner_const_of_vector μ u hu (b k)
  calc
    _ ≤ ∑ i ∈ s, ‖v i‖ ^ 2 := Finset.sum_le_sum hv
    _ = ∑ k : κ, ∑ i ∈ s, (∫ x, f i x * inner ℝ (b k) (u x) ∂μ) ^ 2 := by
      dsimp only [v]
      simp_rw [← b.sum_sq_inner_right, ← integral_scalar_vector_pairing μ _ u (hf _) hu]
      exact Finset.sum_comm
    _ ≤ ∑ k : κ, B * ∫ x, (inner ℝ (b k) (u x)) ^ 2 ∂μ :=
      Finset.sum_le_sum (fun k _ => hb _ (hcoord k))
    _ = B * ∫ x, ‖u x‖ ^ 2 ∂μ := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun k _ => (hcoord k).integrable_sq)]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => b.sum_sq_inner_right (u x)

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_OriginalVectorTestBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vector-valued Bessel estimates for dyadic oscillation tests

The scalar Bessel estimate transfers through the Euclidean orthonormal basis
to directional pairings with vector-valued L² functions. The normalization
retains the radius powers and interaction-packing constant, and the resulting
estimate applies to the hard-truncated Riesz transform under its L² bound.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicOscillationTests.vector_bessel {ι : Type*} {n d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι)
    (u : Ambient d → Ambient d) (hu : MemLp u 2 μ)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, F.test i x * inner ℝ (e i) (u x) ∂μ) ^ 2 / F.radius i ^ n ≤
      (4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, ‖u x‖ ^ 2 ∂μ := by
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  have hh := finite_vector_bessel_of_scalar (EuclideanSpace.basisFun (Fin d) ℝ) μ s
    (F.normalized n hJ).test (fun i => ((F.normalized n hJ).memLp_integrable i).1) _
    (fun v hv => (F.normalized n hJ).bessel C G hC hg hlower hc hJ (by positivity) s v hv)
    u hu e he
  simpa only [F.normalized_pairing_sq n hJ] using! hh

theorem DyadicOscillationTests.native_truncation_bessel {ι : Type*} {n d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧
        eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (ε : ℝ) (hε : 0 < ε) (f : Ambient d → ℝ) (hf : MemLp f 2 μ)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (∫ x, F.test i x * inner ℝ (e i) (truncated n μ ε f x) ∂μ) ^ 2 /
      F.radius i ^ n ≤
      ((4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) * interactionPackingConstant n C G c J) *
        (D : ℝ) ^ 2) * ∫ x, f x ^ 2 ∂μ := by
  obtain ⟨hT, hN⟩ := hR ε hε f hf
  have hB : 0 ≤ 4 * (G * J ^ (n + 1) * (2 * J + 1) ^ 2) *
      interactionPackingConstant n C G c J := by
    unfold interactionPackingConstant
    have hG := hg.1
    positivity
  calc
    _ ≤ _ := F.vector_bessel C G hC hg hlower hc hJ s _ hT e he
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (vector_sq_integral_of_native_norm_bound μ f _ hf hT D hN) hB
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_FixedCutoffBessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bessel bounds for fixed-cutoff pairings

Hard-truncation pairing limits transfer the vector-test Bessel estimate to a
finite family of fixed-cutoff scalar pairings. The resulting bound retains the
interaction packing constant and the mass of the common outer ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem DyadicOscillationTests.fixed_cutoff_bessel {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T)
    (houter : ∀ i ∈ s, tsupport (F.test i) ⊆ ball a T)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
      (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)) ^ 2 / F.radius i ^ (p + 1) ≤
      ((4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
        interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2) * μ.real (ball a T) := by
  have hlim (i : ι) (hi : i ∈ s) := fixed_cutoff_hard_pairing_limit p G μ hg a T hT
    (e i) (F.test i) (F.lip i) (F.lipschitz i) (F.center i) (2 * (J * F.radius i))
    (mul_pos (by norm_num) (mul_pos hJ (F.radius_pos i)))
    (by
      intro x hx
      by_contra hn
      exact hx (houter i hi (subset_tsupport _ hn)))
    (by
      intro x hx
      by_contra hn
      have hb := F.support_subset i (subset_tsupport _ hn)
      apply hx
      exact (ball_subset_ball (by have hr := mul_pos hJ (F.radius_pos i); linarith)) hb)
    (F.mean_zero i)
  have ht := tendsto_finsetSum s (fun i hi => ((hlim i hi).pow 2).div_const (F.radius i ^ (p + 1)))
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro k
  obtain ⟨hf, hnorm⟩ := ball_indicator_one_memLp_and_sq_integral (p + 1) G μ hg a T hT
  have hb := F.native_truncation_bessel C G hC hg hlower hc hJ s D hR
    ((1 / 2 : ℝ) ^ k) (pow_pos (by norm_num) k) _ hf e he
  simpa only [hnorm] using! hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_SmallScaleRieszPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem DyadicOscillationTests.small_scale_riesz_packing {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (R T v : ℝ) (hR : 0 < R) (hT : 0 < T) (hv : 0 < v)
    (hsmall : ∀ i ∈ s, 2 * (J * F.radius i) ≤ R)
    (hcontain : ∀ i ∈ s, ball (F.center i) R ⊆ ball a T)
    (htail : ∀ i ∈ s, oscillationTailConstant (p + 1) G J * (F.radius i / R) ≤ v / 2)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) :
    ∑ i ∈ s, F.radius i ^ (p + 1) ≤
      (((4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
        interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2) * μ.real (ball a T)) /
        (v / 2) ^ 2 := by
  have houter : ∀ i ∈ s, tsupport (F.test i) ⊆ ball a T := by
    intro i hi
    have hr := mul_pos hJ (F.radius_pos i)
    exact (F.support_subset i).trans ((ball_subset_ball (by linarith [hsmall i hi])).trans (hcontain i hi))
  have hcut (i : ι) (hi : i ∈ s) : (v / 2) * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)| := by
    have herr := original_test_outer_cutoff_error p G μ hg (e i) (he i hi) (F.test i)
      (F.lip i) (F.lipschitz i) (F.center i) a (F.radius i) J R T (F.radius_pos i)
      hJ hR (hsmall i hi) (hcontain i hi) (F.lip_bound i) (F.support_subset i) (F.mean_zero i)
    have hb := herr.trans (mul_le_mul_of_nonneg_right (htail i hi)
      (pow_nonneg (F.radius_pos i).le (p + 1)))
    have htri := abs_add_le
      (rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i) -
        rieszScalarPairing (p + 1) (μ.restrict (ball a T))
          (F.center i) (2 * (J * F.radius i)) (e i) (F.test i))
      (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i))
    rw [sub_add_cancel] at htri
    linarith [hlarge i hi]
  have hb := F.fixed_cutoff_bessel C G hC hg hlower hc hJ s D hRiesz a T hT houter e he
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < v / 2))).mpr
  calc
    _ = ∑ i ∈ s, (v / 2) ^ 2 * F.radius i ^ (p + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ s, (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)) ^ 2 / F.radius i ^ (p + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (le_div_iff₀ (pow_pos (F.radius_pos i) (p + 1))).mpr
      have hs := mul_self_le_mul_self
        (mul_nonneg (by positivity : 0 ≤ v / 2) (pow_nonneg (F.radius_pos i).le _)) (hcut i hi)
      nlinarith [sq_abs (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
        (F.center i) (2 * (J * F.radius i)) (e i) (F.test i))]
    _ ≤ _ := hb

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_UniformSmallScalePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem smallRieszRadiusFraction_pos (n : ℕ) (G J v : ℝ)
    (hG : 0 ≤ G) (hJ : 0 < J) (hv : 0 < v) :
    0 < smallRieszRadiusFraction n G J v := by
  unfold smallRieszRadiusFraction
  have hK := oscillationTailConstant_nonneg n G J hG hJ.le
  positivity

theorem smallRieszRadiusFraction_bounds (n : ℕ) (G J v r R : ℝ)
    (hG : 0 ≤ G) (hJ : 0 < J) (hr : 0 < r) (hR : 0 < R)
    (hsmall : r ≤ smallRieszRadiusFraction n G J v * R) :
    2 * (J * r) ≤ R ∧ oscillationTailConstant n G J * (r / R) ≤ v / 2 := by
  have hK := oscillationTailConstant_nonneg n G J hG hJ.le
  have hq : r / R ≤ smallRieszRadiusFraction n G J v := (div_le_iff₀ hR).mpr hsmall
  have hg := hq.trans (min_le_left (1 / (2 * J)) (v / (2 * (oscillationTailConstant n G J + 1))))
  have ht := hq.trans (min_le_right (1 / (2 * J)) (v / (2 * (oscillationTailConstant n G J + 1))))
  have hg' := (le_div_iff₀ (by positivity : 0 < 2 * J)).mp hg
  have ht' := (le_div_iff₀ (by positivity : 0 < 2 * (oscillationTailConstant n G J + 1))).mp ht
  constructor
  · have heq : (r / R) * (2 * J) = (2 * (J * r)) / R := by ring
    rw [heq] at hg'
    simpa only [one_mul] using! (div_le_iff₀ hR).mp hg'
  · have hqpos : 0 < r / R := div_pos hr hR
    nlinarith

theorem DyadicOscillationTests.small_scale_packing_on_top_ball {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (R v : ℝ) (hR : 0 < R) (hv : 0 < v)
    (hcenters : ∀ i ∈ s, dist (F.center i) a ≤ R)
    (hsmall : ∀ i ∈ s, F.radius i ≤ smallRieszRadiusFraction (p + 1) G J v * R)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) :
    ∑ i ∈ s, F.radius i ^ (p + 1) ≤
      (((4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
        interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2) * G * 3 ^ (p + 1) /
        (v / 2) ^ 2) * R ^ (p + 1) := by
  have hs (i : ι) (hi : i ∈ s) := smallRieszRadiusFraction_bounds (p + 1) G J v
    (F.radius i) R hg.1 hJ (F.radius_pos i) hR (hsmall i hi)
  have hb := F.small_scale_riesz_packing C G hC hg hlower hc hJ s D hRiesz a R (3 * R) v
    hR (by positivity) hv (fun i hi => (hs i hi).1)
    (fun i hi => ball_subset_outer_of_radius_dist (F.center i) a R (3 * R)
      (by linarith [hcenters i hi]))
    (fun i hi => (hs i hi).2) e he hlarge
  have hm : μ.real (ball a (3 * R)) ≤ G * (3 * R) ^ (p + 1) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hg.1 (pow_nonneg (by positivity) _))
      (hg.2 a _ (by positivity))
  have hB : 0 ≤ (4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
      interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2 := by
    unfold interactionPackingConstant
    have hG := hg.1
    positivity
  calc
    _ ≤ _ := hb
    _ ≤ _ := by
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm hB) (sq_nonneg (v / 2))
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      rw [mul_pow]
      ring

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_RieszOscillationPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Packing for Riesz oscillations

The packing constant combines finitely many coarse levels with the small-scale
Riesz packing estimate. Its positivity yields a packing bound whose constant is
chosen uniformly before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem rieszOscillationPackingConstant_pos (n : ℕ) (C G c J v : ℝ) (D : ℝ≥0) (N : ℕ)
    (hC : 0 < C) (hG : 0 ≤ G) (hc : 0 < c) (hJ : 0 < J) :
    0 < rieszOscillationPackingConstant n C G c J v D N := by
  unfold rieszOscillationPackingConstant interactionPackingConstant
  positivity

theorem DyadicOscillationTests.riesz_oscillation_packing {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (R v : ℝ) (hR : 0 < R) (hv : 0 < v) (N : ℕ)
    (hN : (1 / 2 : ℝ) ^ N ≤ smallRieszRadiusFraction (p + 1) G J v)
    (hcenters : ∀ i ∈ s, dist (F.center i) a ≤ R)
    (hradii : ∀ i ∈ s, F.radius i = R * (1 / 2 : ℝ) ^ F.level i)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1)
    (hlarge : ∀ i ∈ s, v * F.radius i ^ (p + 1) ≤
      |rieszScalarPairing (p + 1) μ (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)|) :
    ∑ i ∈ s, F.radius i ^ (p + 1) ≤
      rieszOscillationPackingConstant (p + 1) C G c J v D N * R ^ (p + 1) := by
  classical
  have hcoarse := F.coarse_level_packing C G hC hg hlower hc s N a R hR hcenters (by
    intro i hi
    rw [hradii i hi]
    exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num)))
  let t := s.filter (fun i => ¬ F.level i < N)
  have hts (i : ι) (hi : i ∈ t) : i ∈ s := (Finset.mem_filter.mp hi).1
  have hfine := F.small_scale_packing_on_top_ball C G hC hg hlower hc hJ t D hRiesz a R v hR hv
    (fun i hi => hcenters i (hts i hi))
    (by
      intro i hi
      rw [hradii i (hts i hi)]
      have hpow : (1 / 2 : ℝ) ^ F.level i ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Nat.le_of_not_gt (Finset.mem_filter.mp hi).2)
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left (hpow.trans hN) hR.le)
    e (fun i hi => he i (hts i hi)) (fun i hi => hlarge i (hts i hi))
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => F.level i < N)]
  have hsum := add_le_add hcoarse hfine
  dsimp only [t] at hsum
  unfold rieszOscillationPackingConstant
  have hmass : 0 ≤ R ^ (p + 1) := pow_nonneg hR.le _
  nlinarith

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Packing_LatticeOscillationCarleson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Carleson packing of bad lattice descendants

Riesz oscillation packing bounds the radii of bad support descendants. The
lattice mass comparison converts this into a mass packing estimate, with a
positive constant uniform over measures satisfying the growth and Riesz bounds.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem bad_support_descendants_radius_packing {p d : ℕ} [Nontrivial (Ambient d)]
    (μ : Measure (Ambient d)) [SFinite μ] (C G J v : ℝ)
    (hC : 0 < C) (hJ : 0 < J) (hv : 0 < v) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (N : ℕ) (hN : (1 / 2 : ℝ) ^ N ≤ smallRieszRadiusFraction (p + 1) G J v)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (s : Finset (BadSupportDescendant (p + 1) μ R hR k z J v)) :
    ∑ i ∈ s, i.val.radius ^ (p + 1) ≤
      rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N *
        (2 * latticeRadius R k) ^ (p + 1) := by
  let F := badCellTestFamily (p + 1) μ R hR k z J v hcore
  exact F.riesz_oscillation_packing C G hC hg hlower (by norm_num) hJ s D hRiesz
    (z : Ambient d) (2 * latticeRadius R k) v
    (mul_pos (by norm_num) (latticeRadius_pos R hR k)) hv N hN
    (fun i _ => i.val.center_dist_top) (fun i _ => i.val.binary_radius)
    (fun i => (badCellWitness (p + 1) μ R hR k z J v i).direction)
    (fun i _ => (badCellWitness (p + 1) μ R hR k z J v i).direction_bound)
    (fun i _ => (badCellWitness (p + 1) μ R hR k z J v i).large_pairing.le)

theorem bad_support_descendants_mass_packing {p d : ℕ} [Nontrivial (Ambient d)]
    (μ : Measure (Ambient d)) [SFinite μ] (C G J v : ℝ)
    (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v)
    (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (D : ℝ≥0)
    (hRiesz : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (N : ℕ) (hN : (1 / 2 : ℝ) ^ N ≤ smallRieszRadiusFraction (p + 1) G J v)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (s : Finset (BadSupportDescendant (p + 1) μ R hR k z J v)) :
    ∑ i ∈ s, μ.real i.val.cell ≤
      latticeMassPackingConstant (p + 1) C G
        (rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N) *
          μ.real (cleanSupportCell μ R hR k z) := by
  exact cell_mass_packing_of_radius_packing
    (ι := BadSupportDescendant (p + 1) μ R hR k z J v) (n := p + 1) (d := d)
    μ C G (rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N) hC hG
    (rieszOscillationPackingConstant_pos (p + 1) C G (1 / 8) J v D N hC hG.le
      (by norm_num) hJ).le hg hlower R hR k hcore z
    (fun i : BadSupportDescendant (p + 1) μ R hR k z J v => i.val) s
    (bad_support_descendants_radius_packing μ C G J v hC hJ hv hg hlower D hRiesz
      N hN R hR k z hcore s)

theorem exists_uniform_bad_cell_carleson_constant (p d : ℕ) [Nontrivial (Ambient d)]
    (C G J v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ ε f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∀ s : Finset (BadSupportDescendant (p + 1) μ R hR k z J v),
        ∑ i ∈ s, μ.real i.val.cell ≤ K * μ.real (cleanSupportCell μ R hR k z) := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (smallRieszRadiusFraction_pos (p + 1) G J v hG.le hJ hv)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let B := rieszOscillationPackingConstant (p + 1) C G (1 / 8) J v D N
  have hB : 0 < B := rieszOscillationPackingConstant_pos (p + 1) C G (1 / 8) J v D N
    hC hG.le (by norm_num) hJ
  refine ⟨latticeMassPackingConstant (p + 1) C G B,
    latticeMassPackingConstant_pos (p + 1) C G B hC hG hB, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore s
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  exact bad_support_descendants_mass_packing μ C G J v hC hG hJ hv hg hlower D hRiesz
    N hN.le R hR k z hcore s

end

end RieszRectifiability

end OAI
end

section
-- module Solutions.OAIQ231_RR.RieszRectifiability_Nets_LatticeOscillationTotalMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem measure_tsum_le_of_real_finset_bounds {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : ι → Set X) (B : ℝ)
    (hfinite : ∀ i, μ (A i) ≠ ∞)
    (hbound : ∀ s : Finset ι, ∑ i ∈ s, μ.real (A i) ≤ B) :
    ∑' i, μ (A i) ≤ ENNReal.ofReal B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have heq : ∑ i ∈ s, μ (A i) = ENNReal.ofReal (∑ i ∈ s, μ.real (A i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro i _
    exact (ENNReal.ofReal_toReal (hfinite i)).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (hbound s)

theorem exists_uniform_bad_descendant_total_mass_oai (p d : ℕ) [Nontrivial (Ambient d)]
    (C G J v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hJ : 0 < J) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ ε f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
        ∑' i : BadSupportDescendant (p + 1) μ R hR k z J v, μ i.val.cell ≤
          ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_cell_carleson_constant p d C G J v D hC hG hJ hv
  refine ⟨K, hK, ?_⟩
  intro μ hg hlower hRiesz R hR k z hcore
  have hb := measure_tsum_le_of_real_finset_bounds μ
    (fun i : BadSupportDescendant (p + 1) μ R hR k z J v => i.val.cell)
    (K * μ.real (cleanSupportCell μ R hR k z))
    (fun i => ((i.val.measure_upper G hg).trans_lt ENNReal.ofReal_lt_top).ne)
    (hpack μ hg hlower hRiesz R hR k z hcore)
  have hf := (cleanSupportCell_measure_pos_finite μ C G hC hG hg hlower R hR k hcore z).2.ne
  simpa only [ENNReal.ofReal_mul hK.le, Measure.real, ENNReal.ofReal_toReal hf] using! hb

end

end RieszRectifiability

end OAI
end

theorem solution : type_of% @OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass_oai := @OAI.RieszRectifiability.exists_uniform_bad_descendant_total_mass_oai
