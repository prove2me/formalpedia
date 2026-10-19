-- Prove2me | solution 1 for OAI.GaussianPropeller.all_partitions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:23:38.759193+00:00
-- url     : https://prove2.me/submissions/ad197ba8-91c6-4016-b39e-9e699b1ff6ed

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_HairerSPDE_CameronMartin
import Definitions.Def_OAIQWGP000
import Theorems.Thm_OAI_GaussianPropeller_Reduction_Configuration_impossible_four
import Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_configuration

section
-- module Solutions.OAIQW_GaussianPropeller.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_GaussianPropeller.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem integrable_id_gaussian (d : ℕ) :
    Integrable (fun x : Space d => x) (gaussian d) := by
  exact IsGaussian.integrable_id (μ := stdGaussian (Space d))

theorem integrable_id_restrict (d : ℕ) (A : Set (Space d)) :
    Integrable (fun x : Space d => x) ((gaussian d).restrict A) :=
  (integrable_id_gaussian d).restrict

theorem value_nonneg {d k : ℕ} (A : Fin k → Set (Space d)) : 0 ≤ value A := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖centroid (A i)‖)

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Dual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

theorem le_scoreMax (v : Fin k → Space d) (i : Fin k) (x : Space d) :
    ⟪v i, x⟫ ≤ scoreMax v x := by
  exact Finset.le_sup' (fun j => ⟪v j, x⟫) (Finset.mem_univ i)

theorem scoreMax_le_iff (v : Fin k → Space d) (x : Space d) (b : ℝ) :
    scoreMax v x ≤ b ↔ ∀ i, ⟪v i, x⟫ ≤ b := by
  simp only [scoreMax, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem exists_scoreMax (v : Fin k → Space d) (x : Space d) :
    ∃ i, ⟪v i, x⟫ = scoreMax v x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ⟪v i, x⟫)
  exact ⟨i, hi.symm⟩

theorem continuous_scoreMax (v : Fin k → Space d) : Continuous (scoreMax v) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun _ _ => by fun_prop)

theorem norm_scoreMax_le (v : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x‖ ≤ ‖v‖ * ‖x‖ := by
  obtain ⟨i, hi⟩ := exists_scoreMax v.ofLp x
  rw [← hi]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg x))

theorem integrable_scoreMax (v : Tuple d k) :
    Integrable (scoreMax v.ofLp) (gaussian d) := by
  apply ((integrable_id_gaussian d).norm.const_mul ‖v‖).mono'
    (continuous_scoreMax v.ofLp).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_scoreMax_le v)

theorem scoreMax_sub_le (v w : Tuple d k) (x : Space d) :
    scoreMax v.ofLp x - scoreMax w.ofLp x ≤ ‖v - w‖ * ‖x‖ := by
  rw [sub_le_iff_le_add]
  apply (scoreMax_le_iff _ _ _).mpr
  intro i
  have hinner := real_inner_le_norm (v.ofLp i - w.ofLp i) x
  have hcoord : ‖v.ofLp i - w.ofLp i‖ ≤ ‖v - w‖ := PiLp.norm_apply_le (v - w) i
  have hmul := mul_le_mul_of_nonneg_right hcoord (norm_nonneg x)
  rw [inner_sub_left] at hinner
  linarith [le_scoreMax w.ofLp i x]

theorem norm_scoreMax_sub_le (v w : Tuple d k) (x : Space d) :
    ‖scoreMax v.ofLp x - scoreMax w.ofLp x‖ ≤ ‖v - w‖ * ‖x‖ := by
  rw [Real.norm_eq_abs, abs_le]
  have h := scoreMax_sub_le w v x
  rw [norm_sub_rev] at h
  exact ⟨by linarith, scoreMax_sub_le v w x⟩

theorem width_lipschitz_bound (v w : Tuple d k) :
    ‖width v - width w‖ ≤ (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖ := by
  rw [width, width, ← integral_sub (integrable_scoreMax v) (integrable_scoreMax w)]
  calc
    ‖∫ x, scoreMax v.ofLp x - scoreMax w.ofLp x ∂gaussian d‖ ≤
        ∫ x : Space d, ‖v - w‖ * ‖x‖ ∂gaussian d :=
      norm_integral_le_of_norm_le ((integrable_id_gaussian d).norm.const_mul _)
        (Filter.Eventually.of_forall (norm_scoreMax_sub_le v w))
    _ = (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖ := by
      rw [integral_const_mul, mul_comm]

theorem continuous_width : Continuous (width : Tuple d k → ℝ) := by
  let K : NNReal := ⟨∫ x : Space d, ‖x‖ ∂gaussian d,
    integral_nonneg (fun x => norm_nonneg x)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).continuous
  intro v w
  change ‖width v - width w‖ ≤ (∫ x : Space d, ‖x‖ ∂gaussian d) * ‖v - w‖
  exact width_lipschitz_bound v w

omit [NeZero k] in
theorem measurable_scoreCell (v : Fin k → Space d) (i : Fin k) :
    MeasurableSet (scoreCell v i) := by
  change MeasurableSet ({x | ∀ j, ⟪v j, x⟫ ≤ ⟪v i, x⟫} ∩
    {x | ∀ j, j < i → ⟪v j, x⟫ < ⟪v i, x⟫})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    by_cases h : j < i
    · simpa [h] using
        (measurableSet_lt (show Measurable (fun x : Space d => ⟪v j, x⟫) by fun_prop)
          (show Measurable (fun x : Space d => ⟪v i, x⟫) by fun_prop))
    · simp [h]

theorem exists_unique_scoreCell (v : Fin k → Space d) (x : Space d) :
    ∃! i, x ∈ scoreCell v i := by
  classical
  let s := Finset.univ.filter (fun i => ⟪v i, x⟫ = scoreMax v x)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := exists_scoreMax v x
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i := s.min' hs
  have hmax : ⟪v i, x⟫ = scoreMax v x := (Finset.mem_filter.mp (s.min'_mem hs)).2
  have hi : x ∈ scoreCell v i := by
    constructor
    · intro j
      rw [hmax]
      exact le_scoreMax v j x
    · intro j hji
      have hle : ⟪v j, x⟫ ≤ ⟪v i, x⟫ := hmax ▸ le_scoreMax v j x
      apply lt_of_le_of_ne hle
      intro heq
      have hmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, heq.trans hmax⟩
      exact (not_lt_of_ge (s.min'_le j hmem)) hji
  refine ⟨i, hi, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    have hlt : i < j := lt_of_not_ge h
    exact (not_lt_of_ge (hi.1 j)) (hj.2 i hlt)
  · by_contra h
    have hlt : j < i := lt_of_not_ge h
    exact (not_lt_of_ge (hj.1 i)) (hi.2 j hlt)

theorem scoreCell_partition (v : Fin k → Space d) : IsPartition (scoreCell v) :=
  ⟨measurable_scoreCell v, Filter.Eventually.of_forall (exists_unique_scoreCell v)⟩

theorem scoreCell_score (v : Fin k → Space d) {i : Fin k} {x : Space d}
    (hx : x ∈ scoreCell v i) : ⟪v i, x⟫ = scoreMax v x := by
  exact le_antisymm (le_scoreMax v i x) ((scoreMax_le_iff _ _ _).mpr hx.1)

omit [NeZero k] in
theorem norm_moments_sq (A : Fin k → Set (Space d)) : ‖moments A‖ ^ 2 = value A :=
  PiLp.norm_sq_eq_of_L2 _ _

omit [NeZero k] in
theorem pairing_integral {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) :
    ⟪v, moments A⟫ = ∫ x, ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x
      ∂gaussian d := by
  rw [PiLp.inner_apply, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hA.1 i), integral_inner (integrable_id_restrict d (A i))]
    rfl
  · intro i _
    exact ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i)

theorem pairing_le_width {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by
  classical
  rw [pairing_integral hA]
  have hi : Integrable (fun x => ∑ i, (A i).indicator (fun x => ⟪v.ofLp i, x⟫) x)
      (gaussian d) := integrable_finsetSum _ (fun i _ =>
        ((integrable_id_gaussian d).const_inner (v.ofLp i)).indicator (hA.1 i))
  apply integral_mono_ae hi (integrable_scoreMax v)
  filter_upwards [hA.2] with x hx
  obtain ⟨i, hi, huniq⟩ := hx
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using le_scoreMax v.ofLp i x
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem pairing_scoreCell (v : Tuple d k) :
    ⟪v, moments (scoreCell v.ofLp)⟫ = width v := by
  classical
  rw [pairing_integral (scoreCell_partition v.ofLp)]
  apply integral_congr_ae
  filter_upwards [] with x
  obtain ⟨i, hi, huniq⟩ := exists_unique_scoreCell v.ofLp x
  rw [Finset.sum_eq_single i]
  · simpa only [Set.indicator_of_mem hi] using scoreCell_score v.ofLp hi
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => hji (huniq j hj)) _
  · simp

theorem width_nonneg (v : Tuple d k) : 0 ≤ width v := by
  let i : Fin k := ⟨0, NeZero.pos k⟩
  have h := integral_mono_ae ((integrable_id_gaussian d).const_inner (v.ofLp i))
    (integrable_scoreMax v) (Filter.Eventually.of_forall (le_scoreMax v.ofLp i))
  have hzero : (∫ x : Space d, x ∂gaussian d) = 0 := integral_id_stdGaussian
  rw [integral_inner (integrable_id_gaussian d), hzero, inner_zero_right] at h
  exact h

theorem exists_max_width [NeZero d] :
    ∃ v : Tuple d k, ‖v‖ = 1 ∧ ∀ w : Tuple d k, ‖w‖ = 1 → width w ≤ width v := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_sphere (0 : Tuple d k) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    continuous_width.continuousOn
  refine ⟨v, ?_, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hv
  · intro w hw
    apply hmax
    simpa only [Metric.mem_sphere, dist_zero_right] using hw

theorem norm_moments_le {v : Tuple d k}
    (hmax : ∀ w : Tuple d k, ‖w‖ = 1 → width w ≤ width v)
    {A : Fin k → Set (Space d)} (hA : IsPartition A) : ‖moments A‖ ≤ width v := by
  by_cases hz : moments A = 0
  · simpa only [hz, norm_zero] using width_nonneg v
  have hn : ‖moments A‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w : Tuple d k := ‖moments A‖⁻¹ • moments A
  have hw : ‖w‖ = 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]
  have h := (pairing_le_width hA w).trans (hmax w hw)
  have heq : ⟪w, moments A⟫ = ‖moments A‖ := by
    dsimp [w]
    rw [inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    field_simp
  rwa [heq] at h

theorem exists_optimal_partition [NeZero d] :
    ∃ A : Fin k → Set (Space d), IsPartition A ∧
      ∀ B : Fin k → Set (Space d), IsPartition B → value B ≤ value A := by
  obtain ⟨v, hv, hmax⟩ := exists_max_width (d := d) (k := k)
  let A := scoreCell v.ofLp
  have hA := scoreCell_partition v.ofLp
  have hnorm : ‖moments A‖ = width v := by
    apply le_antisymm (norm_moments_le hmax hA)
    rw [← pairing_scoreCell]
    simpa only [hv, one_mul] using real_inner_le_norm v (moments A)
  refine ⟨A, hA, ?_⟩
  intro B hB
  have hnormB := norm_moments_le hmax hB
  rw [← hnorm] at hnormB
  rw [← norm_moments_sq, ← norm_moments_sq]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hnormB

theorem exists_minimal_optimal [NeZero d] :
    ∃ A : Fin k → Set (Space d), MinimalOptimal A := by
  classical
  have hex : ∃ n, ∃ A : Fin k → Set (Space d), Optimal A ∧ activeCount A = n := by
    obtain ⟨A, hA⟩ := exists_optimal_partition (d := d) (k := k)
    exact ⟨activeCount A, A, hA, rfl⟩
  obtain ⟨A, hA, hn⟩ := Nat.find_spec hex
  refine ⟨A, hA, ?_⟩
  intro B hB
  rw [hn]
  exact Nat.find_min' hex ⟨B, hB, rfl⟩

omit [NeZero k] in
theorem centroid_eq_zero_of_null {A : Set (Space d)} (hA : gaussian d A = 0) : centroid A = 0 := by
  unfold centroid
  rw [Measure.restrict_eq_zero.mpr hA, integral_zero_measure]

omit [NeZero k] in

theorem gaussian_hyperplane_null (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by
  let L : StrongDual ℝ (Space d) := innerSL ℝ z
  have hL : L ≠ 0 := by
    intro heq
    have hx : ⟪z, z⟫ = 0 := by
      have h := DFunLike.congr_fun heq z
      simpa [L] using h
    exact hz (inner_self_eq_zero.mp hx)
  have hv : (variance L (stdGaussian (Space d))).toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
  have instN : NullSingletonClass
      (gaussianReal (∫ x, L x ∂stdGaussian (Space d))
        (variance L (stdGaussian (Space d))).toNNReal) := nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {c}) (IsGaussian.map_eq_gaussianReal
    (μ := stdGaussian (Space d)) L)
  rw [Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
    measure_singleton] at h
  exact h

omit [NeZero k] in
theorem measurableSet_closedCell (z : Fin k → Space d) (i : Fin k) :
    MeasurableSet (closedCell z i) := by
  unfold closedCell
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun j => measurableSet_le
    (by fun_prop) (by fun_prop))

end Reduction

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Analytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic

theorem integral_pos_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ in Ioi 0, r * Real.exp (-b * r ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := ne_of_gt hb
  have hd (x : ℝ) : HasDerivAt (fun x => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    apply (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)).congr_deriv
    field_simp [hb']
    ring
  have ht : Tendsto (fun y : ℝ => -(2 * b)⁻¹ * Real.exp (-b * y ^ 2))
      atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    apply Tendsto.const_mul
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn ht using 1
  simp

theorem integral_abs_mul_exp {b : ℝ} (hb : 0 < b) :
    ∫ r : ℝ, |r| * Real.exp (-b * r ^ 2) = b⁻¹ := by
  let f : ℝ → ℝ := fun r => |r| * Real.exp (-b * r ^ 2)
  have hf : Integrable f := by
    simpa only [f, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hb).abs
  have hpos : ∫ r in Ioi 0, f r = (2 * b)⁻¹ := by
    rw [← integral_pos_mul_exp hb]
    exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by
      simp only [f, abs_of_pos (show (0 : ℝ) < r from hr)])
  have hneg : ∫ r in Iic 0, f r = ∫ r in Ioi 0, f r := by
    calc
      ∫ r in Iic 0, f r = ∫ r in Ioi 0, f (-r) := by
        simpa [f] using (integral_comp_neg_Ioi 0 f).symm
      _ = ∫ r in Ioi 0, f r := by simp only [f, abs_neg, neg_sq]
  change (∫ r, f r) = _
  rw [← integral_add_compl measurableSet_Ioi hf, compl_Ioi, hneg, hpos]
  field_simp
  ring

theorem integral_abs_gaussianReal_std :
    ∫ x : ℝ, |x| ∂gaussianReal 0 1 = 2 / Real.sqrt (2 * Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        (|x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) := by
    ext x
    simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
    rw [show -(x ^ 2) / (2 : ℝ) = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [hfun, integral_const_mul, integral_abs_mul_exp (by norm_num : (0 : ℝ) < 1/2)]
  norm_num
  ring

theorem integral_abs_dual_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    ∫ x, |L x| ∂stdGaussian E = ‖L‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  have hm : (stdGaussian E).map L = (gaussianReal 0 1).map (‖L‖ * ·) := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one, Real.toNNReal_of_nonneg (sq_nonneg ‖L‖)]
  rw [← integral_map L.continuous.aemeasurable (by fun_prop :
    AEStronglyMeasurable (fun x : ℝ => |x|) ((stdGaussian E).map L)), hm,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (norm_nonneg L)]
  rw [integral_const_mul, integral_abs_gaussianReal_std]

theorem integral_abs_inner_stdGaussian {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    ∫ x, |⟪v, x⟫| ∂stdGaussian E = ‖v‖ * (2 / Real.sqrt (2 * Real.pi)) := by
  simpa only [InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.norm_map] using
    integral_abs_dual_stdGaussian (InnerProductSpace.toDual ℝ E v)

end GaussianPropeller.Analytic

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Attainment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem integral_comp_neg {d : ℕ} (f : Space d → ℝ) (hf : AEStronglyMeasurable f (gaussian d)) :
    ∫ x, f (-x) ∂gaussian d = ∫ x, f x ∂gaussian d := by
  have hm : (gaussian d).map (fun x => -x) = gaussian d :=
    stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  rw [← integral_map (by fun_prop) (hm.symm ▸ hf), hm]

theorem scoreMax_three {d : ℕ} (v : Fin 3 → Space d) (x : Space d) :
    scoreMax v x = max ⟪v 0, x⟫ (max ⟪v 1, x⟫ ⟪v 2, x⟫) := by
  apply le_antisymm
  · apply (scoreMax_le_iff v x _).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact max_le (le_scoreMax v 0 x) (max_le (le_scoreMax v 1 x) (le_scoreMax v 2 x))

theorem three_range_identity (a b c : ℝ) :
    max a (max b c) + max (-a) (max (-b) (-c)) =
      (|a - b| + |a - c| + |b - c|) / 2 := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · simp [max_eq_right hbc, max_eq_right (hab.trans hbc),
        max_eq_left (neg_le_neg hbc), max_eq_left (neg_le_neg hab),
        abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hbc),
        abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc))]
      ring
    · rcases le_total a c with hac | hca
      · simp [max_eq_left hcb, max_eq_right hab,
          max_eq_right (neg_le_neg hcb), max_eq_left (neg_le_neg hac),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hac),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
      · simp [max_eq_left hcb, max_eq_right hab,
          max_eq_right (neg_le_neg hcb), max_eq_right (neg_le_neg hca),
          abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring
  · rcases le_total a c with hac | hca
    · simp [max_eq_right (hba.trans hac), max_eq_right hac,
        max_eq_left (neg_le_neg (hba.trans hac)), max_eq_right (neg_le_neg hba),
        abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonpos (sub_nonpos.mpr hac),
        abs_of_nonpos (sub_nonpos.mpr (hba.trans hac))]
      ring
    · rcases le_total b c with hbc | hcb
      · simp [max_eq_right hbc, max_eq_left hca,
          max_eq_left (neg_le_neg hbc), max_eq_right (neg_le_neg hba),
          abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonpos (sub_nonpos.mpr hbc)]
        ring
      · simp [max_eq_left hcb, max_eq_left hba,
          max_eq_right (neg_le_neg hcb), max_eq_right (neg_le_neg hca),
          abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca),
          abs_of_nonneg (sub_nonneg.mpr hcb)]
        ring

theorem width_three {d : ℕ} (v : Tuple d 3) :
    width v = (‖v.ofLp 0 - v.ofLp 1‖ + ‖v.ofLp 0 - v.ofLp 2‖ +
      ‖v.ofLp 1 - v.ofLp 2‖) / (2 * Real.sqrt (2 * Real.pi)) := by
  have he (x : Space d) : scoreMax v.ofLp x + scoreMax v.ofLp (-x) =
      (|⟪v.ofLp 0 - v.ofLp 1, x⟫| + |⟪v.ofLp 0 - v.ofLp 2, x⟫| +
        |⟪v.ofLp 1 - v.ofLp 2, x⟫|) / 2 := by
    simp only [scoreMax_three, inner_neg_right, inner_sub_left]
    exact three_range_identity _ _ _
  have hi (w : Space d) : Integrable (fun x => |⟪w, x⟫|) (gaussian d) :=
    ((integrable_id_gaussian d).const_inner w).abs
  have hneg : Integrable (fun x => scoreMax v.ofLp (-x)) (gaussian d) := by
    convert integrable_scoreMax (-v) using 1
    ext x
    simp only [scoreMax_three, PiLp.neg_apply, inner_neg_left, inner_neg_right]
  have h := integral_congr_ae (μ := gaussian d) (Filter.Eventually.of_forall he)
  rw [integral_add (integrable_scoreMax v) hneg,
    integral_comp_neg _ (integrable_scoreMax v).aestronglyMeasurable,
    integral_div] at h
  rw [integral_add (f := fun x => |⟪v.ofLp 0 - v.ofLp 1, x⟫| +
      |⟪v.ofLp 0 - v.ofLp 2, x⟫|) (g := fun x => |⟪v.ofLp 1 - v.ofLp 2, x⟫|)
      ((hi _).add (hi _)) (hi _), integral_add (hi _) (hi _)] at h
  simp_rw [gaussian, Analytic.integral_abs_inner_stdGaussian] at h
  change width v + width v = _ at h
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp [hs] at h ⊢
  nlinarith only [h]

theorem perimeter_sq_le {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      9 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
  have hcs : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      3 * (‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2) := by
    nlinarith [sq_nonneg (‖a-b‖ - ‖a-c‖), sq_nonneg (‖a-b‖ - ‖b-c‖),
      sq_nonneg (‖a-c‖ - ‖b-c‖)]
  have hid : ‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2 =
      3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) - ‖a+b+c‖^2 := by
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
    ring
  rw [hid] at hcs
  nlinarith [sq_nonneg ‖a+b+c‖]

theorem width_three_sq_le {d : ℕ} (v : Tuple d 3) :
    (width v)^2 ≤ (9 / (8 * Real.pi)) * ‖v‖^2 := by
  have hp := perimeter_sq_le (v.ofLp 0) (v.ofLp 1) (v.ofLp 2)
  have hnorm : ‖v‖^2 = ‖v.ofLp 0‖^2 + ‖v.ofLp 1‖^2 + ‖v.ofLp 2‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rw [← hnorm] at hp
  rw [width_three, div_pow]
  have hs : (2 * Real.sqrt (2 * Real.pi))^2 = 8 * Real.pi := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hs]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
  calc
    _ ≤ 9 * ‖v‖^2 := hp
    _ = 9 / (8 * Real.pi) * ‖v‖^2 * (8 * Real.pi) := by
      field_simp

theorem three_partition_bound {d : ℕ} {A : Fin 3 → Set (Space d)} (hA : IsPartition A) :
    value A ≤ 9 / (8 * Real.pi) := by
  have hpair : value A ≤ width (moments A) := by
    simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using
      pairing_le_width hA (moments A)
  have hsq := width_three_sq_le (moments A)
  rw [norm_moments_sq] at hsq
  have hn := value_nonneg A
  have hw : 0 ≤ width (moments A) := hn.trans hpair
  have hval := (sq_le_sq₀ hn hw).mpr hpair
  have hB : (0 : ℝ) < 9 / (8 * Real.pi) := by positivity
  nlinarith

theorem centroid_congr_ae {d : ℕ} {A B : Set (Space d)}
    (h : A =ᵐ[gaussian d] B) : centroid A = centroid B := by
  exact setIntegral_congr_set h

theorem value_congr_ae {d k : ℕ} {A B : Fin k → Set (Space d)}
    (h : ∀ i, A i =ᵐ[gaussian d] B i) : value A = value B := by
  apply Finset.sum_congr rfl
  intro i _
  rw [centroid_congr_ae (h i)]

theorem partition_congr_ae {d k : ℕ} {A B : Fin k → Set (Space d)}
    (hA : IsPartition A) (hB : ∀ i, MeasurableSet (B i))
    (h : ∀ i, A i =ᵐ[gaussian d] B i) : IsPartition B := by
  refine ⟨hB, ?_⟩
  have hh := ae_all_iff.mpr h
  filter_upwards [hA.2, hh] with x hx heq
  change ∀ i, (x ∈ A i) = (x ∈ B i) at heq
  obtain ⟨i, hi, hu⟩ := hx
  exact ⟨i, Eq.mp (heq i) hi, fun j hj => hu j (Eq.mpr (heq j) hj)⟩

theorem closedCell_eq_scoreCell_ae {d k : ℕ} (v : Fin k → Space d)
    (hv : Function.Injective v) (i : Fin k) :
    closedCell v i =ᵐ[gaussian d] scoreCell v i := by
  have ht (j : Fin k) (hij : i ≠ j) : ∀ᵐ x ∂gaussian d, ⟪v i, x⟫ ≠ ⟪v j, x⟫ := by
    rw [ae_iff]
    simpa only [not_not, inner_sub_left, sub_eq_zero] using
      gaussian_hyperplane_null (v i - v j) (sub_ne_zero.mpr (hv.ne hij)) 0
  have ht' := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun hij => ht j hij))
  filter_upwards [ht'] with x hx
  apply propext
  constructor
  · intro hc
    refine ⟨hc, fun j hji => ?_⟩
    exact lt_of_le_of_ne (hc j) (Ne.symm (hx j (ne_of_gt hji)))
  · exact fun hc => hc.1

theorem axis_inner (d : ℕ) (hd : 2 ≤ d) :
    ⟪axis0 d hd, axis0 d hd⟫ = 1 ∧ ⟪axis1 d hd, axis1 d hd⟫ = 1 ∧
      ⟪axis0 d hd, axis1 d hd⟫ = 0 ∧ ⟪axis1 d hd, axis0 d hd⟫ = 0 := by
  simp [axis0, axis1, EuclideanSpace.inner_single_left]

theorem sectorScores_scores (d : ℕ) (hd : 2 ≤ d) (x : Space d) :
    ⟪(sectorScores d hd).ofLp 0, x⟫ = 2 * Real.sqrt 3 * coord 0 x ∧
    ⟪(sectorScores d hd).ofLp 1, x⟫ = -Real.sqrt 3 * coord 0 x + 3 * coord 1 x ∧
    ⟪(sectorScores d hd).ofLp 2, x⟫ = -Real.sqrt 3 * coord 0 x - 3 * coord 1 x := by
  simp [sectorScores, axis0, axis1, coord, show 0 < d by omega, show 1 < d by omega,
    inner_add_left, inner_sub_left, inner_smul_left, EuclideanSpace.inner_single_left]

theorem sectorScores_closed (d : ℕ) (hd : 2 ≤ d) (i : Fin 3) :
    closedCell (sectorScores d hd).ofLp i = propeller d 3 i := by
  ext x
  obtain ⟨h0, h1, h2⟩ := sectorScores_scores d hd x
  fin_cases i <;>
    simp [closedCell, propeller, Fin.forall_fin_succ, h0, h1, h2, abs_le] <;>
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

theorem sectorScores_norms (d : ℕ) (hd : 2 ≤ d) :
    ‖sectorScores d hd‖^2 = 36 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 1‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 2‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 1 - (sectorScores d hd).ofLp 2‖ = 6 := by
  obtain ⟨h00, h11, h01, h10⟩ := axis_inner d hd
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn (x : Space d) : ‖x‖^2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
  constructor
  · rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    change ‖(2 * Real.sqrt 3) • axis0 d hd‖^2 +
      ‖(-Real.sqrt 3) • axis0 d hd + (3 : ℝ) • axis1 d hd‖^2 +
      ‖(-Real.sqrt 3) • axis0 d hd - (3 : ℝ) • axis1 d hd‖^2 = 36
    simp only [hn, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      h00, h01, h10, h11, starRingEnd_apply, star_trivial]
    nlinarith only [hs]
  · have hsq (i j : Fin 3) (hij : i ≠ j) :
        ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖^2 = 36 := by
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals dsimp [sectorScores]
      all_goals simp only [hn, inner_smul_left, inner_smul_right,
        inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        h00, h01, h10, h11, starRingEnd_apply, star_trivial]
      all_goals nlinarith only [hs]
    have he (i j : Fin 3) (hij : i ≠ j) :
        ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖ = 6 := by
      nlinarith [hsq i j hij, norm_nonneg ((sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j)]
    exact ⟨he 0 1 (by decide), he 0 2 (by decide), he 1 2 (by decide)⟩

theorem sectorScores_injective (d : ℕ) (hd : 2 ≤ d) :
    Function.Injective (sectorScores d hd).ofLp := by
  obtain ⟨_, h01, h02, h12⟩ := sectorScores_norms d hd
  intro i j hij
  have hz : ‖(sectorScores d hd).ofLp i - (sectorScores d hd).ofLp j‖ = 0 := by
    rw [hij, sub_self, norm_zero]
  fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev]

theorem propeller_three (d : ℕ) (hd : 2 ≤ d) :
    IsPartition (propeller d 3) ∧ value (propeller d 3) = 9 / (8 * Real.pi) := by
  let v := sectorScores d hd
  have he (i : Fin 3) : propeller d 3 i =ᵐ[gaussian d] scoreCell v.ofLp i := by
    rw [← sectorScores_closed d hd i]
    exact closedCell_eq_scoreCell_ae v.ofLp (sectorScores_injective d hd) i
  have hp : IsPartition (propeller d 3) :=
    partition_congr_ae (scoreCell_partition v.ofLp)
      (fun i => by rw [← sectorScores_closed d hd i]; exact measurableSet_closedCell _ i)
      (fun i => (he i).symm)
  refine ⟨hp, le_antisymm (three_partition_bound hp) ?_⟩
  rw [value_congr_ae he]
  obtain ⟨hv, h01, h02, h12⟩ := sectorScores_norms d hd
  have hw : (width v)^2 = 36 * (9 / (8 * Real.pi)) := by
    rw [width_three, h01, h02, h12, div_pow, mul_pow,
      Real.sq_sqrt (by positivity)]
    field_simp; ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) v (moments (scoreCell v.ofLp))
  rw [pairing_scoreCell, Real.norm_eq_abs] at hcs
  have hs := (sq_le_sq₀ (abs_nonneg (width v))
    (mul_nonneg (norm_nonneg v) (norm_nonneg (moments (scoreCell v.ofLp))))).mpr hcs
  rw [sq_abs, mul_pow, norm_moments_sq, hw] at hs
  change 36 * (9 / (8 * Real.pi)) ≤ ‖sectorScores d hd‖^2 * _ at hs
  rw [hv] at hs
  linarith only [hs]

theorem append_empty_partition {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : IsPartition (Fin.lastCases ∅ A) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.lastCases_last] using (MeasurableSet.empty : MeasurableSet (∅ : Set (Space d)))
    · simpa only [Fin.lastCases_castSucc] using hA.1 j
  · filter_upwards [hA.2] with x hx
    obtain ⟨i, hi, hu⟩ := hx
    refine ⟨i.castSucc, ?_, ?_⟩
    · simpa only [Fin.lastCases_castSucc] using hi
    · intro j
      refine Fin.lastCases ?_ (fun l => ?_) j
      · simp only [Fin.lastCases_last, Set.mem_empty_iff_false, false_implies]
      · intro hj
        exact congrArg Fin.castSucc (hu l (by simpa only [Fin.lastCases_castSucc] using hj))

theorem append_empty_value {d k : ℕ} (A : Fin k → Set (Space d)) :
    value (Fin.lastCases ∅ A) = value A := by
  simp [value, Fin.sum_univ_castSucc]

theorem propeller_succ (d k : ℕ) (hk : 3 ≤ k) :
    propeller d (k+1) = Fin.lastCases ∅ (propeller d k) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [propeller, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  · simp [propeller]

theorem propeller_attainment (d k : ℕ) (hd : 2 ≤ d) (hk : 3 ≤ k) :
    IsPartition (propeller d k) ∧ value (propeller d k) = 9 / (8 * Real.pi) := by
  induction k, hk using Nat.le_induction with
  | base => exact propeller_three d hd
  | succ k hk ih =>
    rw [propeller_succ d k hk]
    exact ⟨append_empty_partition ih.1, (append_empty_value _).trans ih.2⟩

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.ResidualBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem residualCoefficient_pos {z y : Space d} (h : ⟪z,y⟫ < 0) :
    0 < residualCoefficient z y := by
  have hz : z ≠ 0 := by intro hz; simp [hz] at h
  exact div_pos (neg_pos.mpr h) (sq_pos_of_pos (norm_pos_iff.mpr hz))

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Geometry

open scoped RealInnerProductSpace

lemma pair_factor_le_eight {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c ≤ 1) :
    (1 + c)^2 * ((1 + a)^2 + (1 + b)^2) ≤ 8 := by
  have hc1 : c ≤ 1 := by linarith
  have hab : a + b ≤ 1 - c := by linarith
  have hab2 := (sq_le_sq₀ (by linarith : 0 ≤ a+b) (by linarith : 0 ≤ 1-c)).mpr hab
  have hu : (1+a)^2 + (1+b)^2 ≤ (2-c)^2 + 1 := by
    nlinarith only [hab, hab2, mul_nonneg ha hb]
  have hmul := mul_le_mul_of_nonneg_left hu (sq_nonneg (1+c))
  have hc2 := (sq_le_sq₀ hc (by norm_num : (0:ℝ) ≤ 1)).mpr hc1
  have hpos : 0 ≤ (1-c)^2 * (3-c^2) := mul_nonneg (sq_nonneg _) (by nlinarith)
  have hid : 8 - (1+c)^2 * ((2-c)^2+1) = (1-c)^2*(3-c^2) := by ring
  linarith only [hmul, hpos, hid]

lemma triple_factor_le_ten {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c ≤ 1) :
    (1+a)^2*(1+b)^2 + (1+a)^2*(1+c)^2 + (1+b)^2*(1+c)^2 ≤ 10 := by
  let s := a+b+c
  let p := a*b+a*c+b*c
  let q := a*b*c
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := hs
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hs2 : s^2 ≤ 1 := by nlinarith only [hs0, hs1, mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hps : 3*p ≤ s^2 := by
    dsimp [p,s]
    nlinarith only [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
  have hp1 : p ≤ 1/3 := by linarith only [hps,hs2]
  have hsp : s*p ≤ 1/3 := (mul_le_mul_of_nonneg_right hs1 hp0).trans (by simpa using hp1)
  have hp2 : p^2 ≤ 1/9 := by
    have hh := (sq_le_sq₀ hp0 (by norm_num : (0:ℝ) ≤ 1/3)).mpr hp1
    norm_num at hh ⊢
    exact hh
  have hq : 0 ≤ (6+2*s)*q := mul_nonneg (by positivity) hq0
  have hid : (1+a)^2*(1+b)^2 + (1+a)^2*(1+c)^2 + (1+b)^2*(1+c)^2 =
      3+4*s+2*s^2+2*s*p+p^2-(6+2*s)*q := by dsimp [s,p,q]; ring
  rw [hid]
  linarith only [hs1, hs2, hsp, hp2, hq]

lemma row_two_le {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (w : ι → E)
    (hw : ∑ i, w i = 0) (hneg : ∀ i j, i ≠ j → ⟪w i, w j⟫ ≤ 0)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    -⟪w i, w j⟫ - ⟪w i, w k⟫ ≤ ‖w i‖^2 := by
  have hr : ∑ l ∈ Finset.univ.erase i, -⟪w i, w l⟫ = ‖w i‖^2 := by
    have hsum : ∑ l, ⟪w i, w l⟫ = 0 := by rw [← inner_sum, hw, inner_zero_right]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    rw [Finset.sum_neg_distrib, real_inner_self_eq_norm_sq] at *
    linarith only [hsum]
  rw [← hr]
  have hsub : ({j,k} : Finset ι) ⊆ Finset.univ.erase i := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hij.symm]
    · simp [hik.symm]
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun l hl _ => neg_nonneg.mpr (hneg i l (Finset.mem_erase.mp hl).1.symm))
  simpa only [Finset.sum_pair hjk, sub_eq_add_neg] using h

lemma row_determinants_lower {h₁ h₂ h₃ u v : ℝ}
    (hu : u ≤ 0) (hv : v ≤ 0) (hr : -u-v ≤ h₃) :
    h₃*(h₁+h₂-h₃) ≤ (h₃*h₁-u^2)+(h₃*h₂-v^2) := by
  have hp : 0 ≤ -u-v := by linarith
  have hh : 0 ≤ h₃ := hp.trans hr
  have hs := (sq_le_sq₀ hp hh).mpr hr
  nlinarith only [hs, mul_nonneg (neg_nonneg.mpr hu) (neg_nonneg.mpr hv)]

lemma three_correlations_lower {h₁ h₂ h₃ s ρ₁₂ ρ₁₃ ρ₂₃ : ℝ}
    (hs : 0 ≤ s) (hh₁ : s ≤ h₁) (hh₂ : s ≤ h₂) (hh₃ : s ≤ h₃)
    (h₁₂ : -1 ≤ ρ₁₂ ∧ ρ₁₂ ≤ 0) (h₁₃ : -1 ≤ ρ₁₃ ∧ ρ₁₃ ≤ 0)
    (h₂₃ : -1 ≤ ρ₂₃ ∧ ρ₂₃ ≤ 0) (hvar : 0 ≤ 3+2*(ρ₁₂+ρ₁₃+ρ₂₃)) :
    (3/2:ℝ)*s^2 ≤ h₁*h₂*(1-ρ₁₂^2)+h₁*h₃*(1-ρ₁₃^2)+h₂*h₃*(1-ρ₂₃^2) := by
  have hb {x : ℝ} (hx : -1 ≤ x ∧ x ≤ 0) : x^2 ≤ -x := by
    nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ 1+x) (neg_nonneg.mpr hx.2)]
  have hv₁₂ : 0 ≤ 1-ρ₁₂^2 := by nlinarith only [hb h₁₂, h₁₂.1]
  have hv₁₃ : 0 ≤ 1-ρ₁₃^2 := by nlinarith only [hb h₁₃, h₁₃.1]
  have hv₂₃ : 0 ≤ 1-ρ₂₃^2 := by nlinarith only [hb h₂₃, h₂₃.1]
  have hsum : 3/2 ≤ (1-ρ₁₂^2)+(1-ρ₁₃^2)+(1-ρ₂₃^2) := by
    linarith only [hb h₁₂, hb h₁₃, hb h₂₃, hvar]
  have hprod {a b : ℝ} (ha : s ≤ a) (hb : s ≤ b) : s^2 ≤ a*b := by
    simpa only [pow_two] using mul_le_mul ha hb hs (hs.trans ha)
  calc
    (3/2:ℝ)*s^2 ≤ ((1-ρ₁₂^2)+(1-ρ₁₃^2)+(1-ρ₂₃^2))*s^2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg s)
    _ = s^2*(1-ρ₁₂^2)+s^2*(1-ρ₁₃^2)+s^2*(1-ρ₂₃^2) := by ring
    _ ≤ _ := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right (hprod hh₁ hh₂) hv₁₂)
      (mul_le_mul_of_nonneg_right (hprod hh₁ hh₃) hv₁₃))
      (mul_le_mul_of_nonneg_right (hprod hh₂ hh₃) hv₂₃)

section InnerProduct
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma unitVector_norm {w : E} (hw : w ≠ 0) : ‖unitVector w‖ = 1 := by
  simp [unitVector, norm_smul, norm_ne_zero_iff.mpr hw]

lemma unitVector_inner_cancel (u v : E) :
    ‖u‖ * ‖v‖ * ⟪unitVector u, unitVector v⟫ = ⟪u,v⟫ := by
  by_cases hu : u = 0
  · simp [hu, unitVector]
  by_cases hv : v = 0
  · simp [hv, unitVector]
  simp only [unitVector, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hv]

lemma unitVector_inner_nonpos {u v : E} (h : ⟪u,v⟫ ≤ 0) :
    ⟪unitVector u, unitVector v⟫ ≤ 0 := by
  simp only [unitVector, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) h)

lemma unitVector_inner_bounds {u v : E} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ⟪u,v⟫ ≤ 0) :
    -1 ≤ ⟪unitVector u, unitVector v⟫ ∧ ⟪unitVector u, unitVector v⟫ ≤ 0 := by
  have hc := norm_inner_le_norm (𝕜 := ℝ) (unitVector u) (unitVector v)
  rw [unitVector_norm hu, unitVector_norm hv, mul_one, Real.norm_eq_abs] at hc
  exact ⟨(abs_le.mp hc).1, unitVector_inner_nonpos h⟩

lemma unitVector_variance (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    0 ≤ 3 + 2 * (⟪unitVector u, unitVector v⟫ + ⟪unitVector u, unitVector w⟫ +
      ⟪unitVector v, unitVector w⟫) := by
  have h := sq_nonneg ‖unitVector u + unitVector v + unitVector w‖
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_left,
    unitVector_norm hu, unitVector_norm hv, unitVector_norm hw] at h
  nlinarith only [h]

lemma gram_det_unitVector (u v : E) :
    ‖u‖^2 * ‖v‖^2 * (1-⟪unitVector u, unitVector v⟫^2) =
      ‖u‖^2 * ‖v‖^2 - ⟪u,v⟫^2 := by
  calc
    _ = ‖u‖^2*‖v‖^2-(‖u‖*‖v‖*⟪unitVector u, unitVector v⟫)^2 := by ring
    _ = _ := by rw [unitVector_inner_cancel]

lemma three_gram_determinants_lower (u v w : E) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (huv : ⟪u,v⟫ ≤ 0) (huw : ⟪u,w⟫ ≤ 0) (hvw : ⟪v,w⟫ ≤ 0)
    {s : ℝ} (hs : 0 ≤ s) (hsu : s ≤ ‖u‖^2) (hsv : s ≤ ‖v‖^2) (hsw : s ≤ ‖w‖^2) :
    (3/2:ℝ)*s^2 ≤ (‖u‖^2*‖v‖^2-⟪u,v⟫^2) + (‖u‖^2*‖w‖^2-⟪u,w⟫^2) +
      (‖v‖^2*‖w‖^2-⟪v,w⟫^2) := by
  have h := three_correlations_lower hs hsu hsv hsw
    (unitVector_inner_bounds hu hv huv) (unitVector_inner_bounds hu hw huw)
    (unitVector_inner_bounds hv hw hvw) (unitVector_variance u v w hu hv hw)
  simpa only [gram_det_unitVector] using h

lemma gram_det_nonneg (u v : E) : 0 ≤ ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by
  have h := real_inner_mul_inner_self_le u v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h]

lemma first_constraint_of_pair_bounds (u v w : E) {t c L κ a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hsum : a+b+q ≤ 1)
    (hc : t^2 ≤ c) (hw : c-t^2 ≤ ‖w‖^2)
    (hdiag : L-c-2*t^2 ≤ ‖u‖^2+‖v‖^2-‖w‖^2)
    (hwu : ⟪w,u⟫ ≤ 0) (hwv : ⟪w,v⟫ ≤ 0)
    (hrow : -⟪w,u⟫-⟪w,v⟫ ≤ ‖w‖^2)
    (hpair₁ : ‖w‖^2*‖u‖^2-⟪w,u⟫^2 ≤ κ^2*t^2*(1+q)^2*(1+a)^2)
    (hpair₂ : ‖w‖^2*‖v‖^2-⟪w,v⟫^2 ≤ κ^2*t^2*(1+q)^2*(1+b)^2) :
    (c-t^2)*(L-c-2*t^2) ≤ 8*κ^2*t^2 := by
  have hlower : (c-t^2)*(L-c-2*t^2) ≤
      (‖w‖^2*‖u‖^2-⟪w,u⟫^2)+(‖w‖^2*‖v‖^2-⟪w,v⟫^2) := by
    by_cases hsign : 0 ≤ L-c-2*t^2
    · exact (mul_le_mul hw hdiag hsign (sq_nonneg ‖w‖)).trans
        (row_determinants_lower hwu hwv hrow)
    · exact (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc) (le_of_not_ge hsign)).trans
        (add_nonneg (gram_det_nonneg w u) (gram_det_nonneg w v))
  have hu := mul_le_mul_of_nonneg_left (pair_factor_le_eight ha hb hq hsum)
    (mul_nonneg (sq_nonneg κ) (sq_nonneg t))
  nlinarith only [hlower, hpair₁, hpair₂, hu]

lemma second_constraint_of_pair_bounds (u v w : E)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) {t c κ a b q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hsum : a+b+q ≤ 1)
    (hc : t^2 ≤ c) (hsu : c-t^2 ≤ ‖u‖^2) (hsv : c-t^2 ≤ ‖v‖^2)
    (hsw : c-t^2 ≤ ‖w‖^2) (huv : ⟪u,v⟫ ≤ 0) (huw : ⟪u,w⟫ ≤ 0) (hvw : ⟪v,w⟫ ≤ 0)
    (hpair₁ : ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ κ^2*t^2*(1+a)^2*(1+b)^2)
    (hpair₂ : ‖u‖^2*‖w‖^2-⟪u,w⟫^2 ≤ κ^2*t^2*(1+a)^2*(1+q)^2)
    (hpair₃ : ‖v‖^2*‖w‖^2-⟪v,w⟫^2 ≤ κ^2*t^2*(1+b)^2*(1+q)^2) :
    (3/2:ℝ)*(c-t^2)^2 ≤ 10*κ^2*t^2 := by
  have hlow := three_gram_determinants_lower u v w hu hv hw huv huw hvw
    (sub_nonneg.mpr hc) hsu hsv hsw
  have hup := mul_le_mul_of_nonneg_left (triple_factor_le_ten ha hb hq hsum)
    (mul_nonneg (sq_nonneg κ) (sq_nonneg t))
  nlinarith only [hlow, hpair₁, hpair₂, hpair₃, hup]

end InnerProduct

end GaussianPropeller.Geometry

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.FourReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.Reduction
variable {d k : ℕ}

lemma residual_inner_base {z y:Space d} (hz:z≠0) :
    ⟪z,y⟫ = -residualCoefficient z y*‖z‖^2 := by
  unfold residualCoefficient
  field_simp

lemma residual_norm_sq {z y:Space d} (hz:z≠0) :
    ‖residualVector z y‖^2=‖y‖^2-(residualCoefficient z y)^2*‖z‖^2 := by
  rw [residualVector,norm_add_sq_real,real_inner_smul_right,norm_smul]
  rw [real_inner_comm z y,residual_inner_base hz]
  simp only [mul_pow,Real.norm_eq_abs,sq_abs]
  ring

lemma residual_inner {z y v:Space d} (hz:z≠0) :
    ⟪residualVector z y,residualVector z v⟫ =
      ⟪y,v⟫-residualCoefficient z y*residualCoefficient z v*‖z‖^2 := by
  simp only [residualVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq]
  rw [real_inner_comm z y,residual_inner_base hz (y:=y),residual_inner_base hz (y:=v)]
  ring

lemma residual_coefficient_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualCoefficient (z i) (z j)=1 := by
  have hh : ∑ j ∈ Finset.univ.erase i,⟪z i,z j⟫ = -‖z i‖^2 := by
    have he := congrArg (fun y=>⟪z i,y⟫) hsum
    rw [inner_sum,inner_zero_right,← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      real_inner_self_eq_norm_sq] at he
    linarith only [he]
  simp only [residualCoefficient,←Finset.sum_div,Finset.sum_neg_distrib,hh,neg_neg]
  exact div_self (pow_ne_zero _ (norm_ne_zero_iff.mpr hi))

lemma residual_sum (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j ∈ Finset.univ.erase i,residualVector (z i) (z j)=0 := by
  have hh : ∑ j ∈ Finset.univ.erase i,z j = -(z i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  simp only [residualVector,Finset.sum_add_distrib,←Finset.sum_smul,
    residual_coefficient_sum z hsum i hi,one_smul,hh,neg_add_cancel]

end GaussianPropeller.Reduction

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

lemma residual_self (z:Space d) : residualVector z z=0 := by
  by_cases hz:z=0
  · simp [hz,residualVector,residualCoefficient]
  · have hn:‖z‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
    simp [residualVector,residualCoefficient,hn]

lemma residual_sum_all (z:Fin k→Space d) (hsum:∑ j,z j=0) (i:Fin k) (hi:z i≠0) :
    ∑ j,residualVector (z i) (z j)=0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),residual_sum z hsum i hi,residual_self,add_zero]

lemma residual_obtuse (z:Fin k→Space d) (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0))
    (i:Fin k) (hi:z i≠0) {j l:Fin k} (hij:i≠j) (hil:i≠l) (hjl:j≠l) :
    ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫<0 := by
  rw [residual_inner hi]
  have ha:0<residualCoefficient (z i) (z j) := residualCoefficient_pos (hneg hij)
  have hb:0<residualCoefficient (z i) (z l) := residualCoefficient_pos (hneg hil)
  have hh : 0≤residualCoefficient (z i) (z j)*residualCoefficient (z i) (z l)*‖z i‖^2 := by positivity
  linarith only [hneg hjl,hh]

lemma residual_obtuse_all (z:Fin k→Space d) (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0))
    (i:Fin k) (hi:z i≠0) : ∀ j l, j≠l →
    ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫≤0 := by
  intro j l hjl
  by_cases hij:i=j
  · subst j; simp [residual_self]
  by_cases hil:i=l
  · subst l; simp [residual_self]
  exact (residual_obtuse z hneg i hi hij hil hjl).le

lemma residual_coefficients_three (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q) :
    residualCoefficient (z i) (z j)+residualCoefficient (z i) (z l)+
      residualCoefficient (z i) (z q)≤1 := by
  have hsub : ({j,l,q}:Finset (Fin k))⊆Finset.univ.erase i := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl|rfl <;> simp [Ne.symm hij,Ne.symm hil,Ne.symm hiq]
  have h:=Finset.sum_le_sum_of_subset_of_nonneg hsub (f:=fun a=>residualCoefficient (z i) (z a))
    (fun a ha _ => (residualCoefficient_pos (hneg (Finset.mem_erase.mp ha).1.symm)).le)
  rw [residual_coefficient_sum z hsum i hi] at h
  simpa [Finset.sum_insert,Finset.sum_singleton,hjl,hjq,hlq,add_assoc] using h

lemma configuration_determinants (z:Fin k→Space d) (hsum:∑ j,z j=0)
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hi:z i≠0)
    {j l q : Fin k} (hij:i≠j) (hil:i≠l) (hiq:i≠q) (hjl:j≠l) (hjq:j≠q) (hlq:l≠q)
    (hj:‖z q‖≤‖z j‖) (hl:‖z q‖≤‖z l‖) (hmin:‖z i‖≤‖z q‖)
    (hpair:∀ a b, i≠a → i≠b →
      ‖residualVector (z i) (z a)‖^2*‖residualVector (z i) (z b)‖^2-
      ⟪residualVector (z i) (z a),residualVector (z i) (z b)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z a))^2*
      (1+residualCoefficient (z i) (z b))^2) :
    (‖z q‖^2-‖z i‖^2)*(‖z j‖^2+‖z l‖^2-‖z q‖^2-2*‖z i‖^2)≤
      8*(3/Real.pi)^2*‖z i‖^2 ∧
    (3/2:ℝ)*(‖z q‖^2-‖z i‖^2)^2≤10*(3/Real.pi)^2*‖z i‖^2 := by
  let a:=residualCoefficient (z i) (z j)
  let b:=residualCoefficient (z i) (z l)
  let c:=residualCoefficient (z i) (z q)
  let u:=residualVector (z i) (z j)
  let v:=residualVector (z i) (z l)
  let w:=residualVector (z i) (z q)
  have ha:0<a := residualCoefficient_pos (hneg hij)
  have hb:0<b := residualCoefficient_pos (hneg hil)
  have hc:0<c := residualCoefficient_pos (hneg hiq)
  have hs:a+b+c≤1 := residual_coefficients_three z hsum hneg i hi hij hil hiq hjl hjq hlq
  have ha1:a^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hb1:b^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hc1:c^2≤1 := by nlinarith only [ha,hb,hc,hs]
  have hu:‖u‖^2=‖z j‖^2-a^2*‖z i‖^2 := residual_norm_sq hi
  have hv:‖v‖^2=‖z l‖^2-b^2*‖z i‖^2 := residual_norm_sq hi
  have hw:‖w‖^2=‖z q‖^2-c^2*‖z i‖^2 := residual_norm_sq hi
  have ht:‖z i‖^2≤‖z q‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmin
  have hrj:‖z q‖^2≤‖z j‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hj
  have hrl:‖z q‖^2≤‖z l‖^2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hl
  have hla:=mul_le_mul_of_nonneg_right ha1 (sq_nonneg ‖z i‖)
  have hlb:=mul_le_mul_of_nonneg_right hb1 (sq_nonneg ‖z i‖)
  have hlc:=mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖z i‖)
  have hlu:‖z q‖^2-‖z i‖^2≤‖u‖^2 := by nlinarith only [hu,hla,hrj]
  have hlv:‖z q‖^2-‖z i‖^2≤‖v‖^2 := by nlinarith only [hv,hlb,hrl]
  have hlw:‖z q‖^2-‖z i‖^2≤‖w‖^2 := by nlinarith only [hw,hlc]
  have huw:⟪u,w⟫<0 := residual_obtuse z hneg i hi hij hiq hjq
  have hvw:⟪v,w⟫<0 := residual_obtuse z hneg i hi hil hiq hlq
  have huv:⟪u,v⟫<0 := residual_obtuse z hneg i hi hij hil hjl
  have hwu:⟪w,u⟫≤0 := by rw [real_inner_comm u w]; exact huw.le
  have hwv:⟪w,v⟫≤0 := by rw [real_inner_comm v w]; exact hvw.le
  have hrow := Geometry.row_two_le (fun a=>residualVector (z i) (z a))
    (residual_sum_all z hsum i hi) (residual_obtuse_all z hneg i hi) hjq.symm hlq.symm hjl
  constructor
  · exact Geometry.first_constraint_of_pair_bounds u v w ha.le hb.le hc.le hs ht hlw
      (by nlinarith only [hu,hv,hw,hla,hlb,mul_nonneg (sq_nonneg c) (sq_nonneg ‖z i‖)])
      hwu hwv hrow (hpair q j hiq hij) (hpair q l hiq hil)
  · have hu0:u≠0 := by intro he; rw [he,inner_zero_left] at huv; exact (lt_irrefl _ huv)
    have hv0:v≠0 := by intro he; rw [he,inner_zero_right] at huv; exact (lt_irrefl _ huv)
    have hw0:w≠0 := by intro he; rw [he,inner_zero_right] at huw; exact (lt_irrefl _ huw)
    exact Geometry.second_constraint_of_pair_bounds u v w hu0 hv0 hw0 ha.le hb.le hc.le hs
      ht hlu hlv hlw huv.le huw.le hvw.le (hpair j l hij hil) (hpair j q hij hiq) (hpair l q hil hiq)

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Scalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller
namespace Scalar

theorem third_radius_gt {L u : ℝ} (hu : 0 < u) (hL : L ≤ 8 / 9)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116) : 0.23 < u := by
  by_contra! h
  have hd : (0.415 : ℝ) / 0.23 ≤ 0.415 / u :=
    div_le_div_of_nonneg_left (by norm_num) hu h
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  norm_num at hm
  nlinarith

theorem small_minimum_interval {L u t a b M : ℝ}
    (ht : 0 ≤ t) (htq : t ≤ 0.066) (hL : L ≤ 8 / 9)
    (hua : a ≤ u) (hub : u ≤ b) (ha : 0.066 < a)
    (hden : 0 < 0.415 / b - 0.734) (hM : 0 ≤ M)
    (hrow : (0.116 : ℝ) ≤
      (1 - (b ^ 2 + 2 * (0.066 : ℝ) ^ 2 + M)) * (0.415 / b - 0.734))
    (hmargin : 8 * (0.066 : ℝ) ^ 2 < (a ^ 2 - (0.066 : ℝ) ^ 2) * M)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116)
    (hdet : (u ^ 2 - t ^ 2) * (L - u ^ 2 - 2 * t ^ 2) ≤ 8 * t ^ 2) : False := by
  have hup : 0 < u := by linarith
  have hb : 0 < b := lt_of_lt_of_le hup hub
  have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 0.415 by norm_num) hup hub
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  have hLc : b ^ 2 + 2 * (0.066 : ℝ) ^ 2 + M ≤ L := by
    have hh := le_of_mul_le_mul_right ((hm.trans hcharge).trans hrow) hden
    linarith
  have hub2 : u ^ 2 ≤ b ^ 2 := by nlinarith
  have hua2 : a ^ 2 ≤ u ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ (0.066 : ℝ) ^ 2 := by nlinarith
  have hfirst : a ^ 2 - (0.066 : ℝ) ^ 2 ≤ u ^ 2 - t ^ 2 := by linarith
  have hfirst0 : 0 ≤ u ^ 2 - t ^ 2 := by nlinarith
  have hsecond : M ≤ L - u ^ 2 - 2 * t ^ 2 := by linarith
  have hp := mul_le_mul hfirst hsecond hM hfirst0
  nlinarith

theorem minimum_gt {L u t : ℝ} (ht : 0 ≤ t) (hu : 0.23 < u)
    (hL : L ≤ 8 / 9) (hL2 : 2 * u ^ 2 ≤ L)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116)
    (hdet : (u ^ 2 - t ^ 2) * (L - u ^ 2 - 2 * t ^ 2) ≤ 8 * t ^ 2) :
    0.066 < t := by
  by_contra! htq
  by_cases hbig : 0.44 ≤ u
  · have ht2 : t ^ 2 ≤ (0.066 : ℝ) ^ 2 := by nlinarith
    have hu2 : (0.44 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith
    have hfirst : (0.44 : ℝ) ^ 2 - (0.066 : ℝ) ^ 2 ≤ u ^ 2 - t ^ 2 := by linarith
    have hsecond : (0.44 : ℝ) ^ 2 - 2 * (0.066 : ℝ) ^ 2 ≤
        L - u ^ 2 - 2 * t ^ 2 := by linarith
    have hp := mul_le_mul hfirst hsecond (by norm_num)
      (show 0 ≤ u ^ 2 - t ^ 2 by nlinarith)
    norm_num at hp
    nlinarith
  · have hb : u ≤ 0.44 := le_of_lt (lt_of_not_ge hbig)
    by_cases h30 : u ≤ 0.30
    · exact small_minimum_interval (a := 0.23) (b := 0.30) (M := 0.72264)
        ht htq hL hu.le h30 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    by_cases h35 : u ≤ 0.35
    · exact small_minimum_interval (a := 0.30) (b := 0.35) (M := 0.61198)
        ht htq hL (by linarith) h35 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    by_cases h41 : u ≤ 0.41
    · exact small_minimum_interval (a := 0.35) (b := 0.41) (M := 0.40621)
        ht htq hL (by linarith) h41 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    · exact small_minimum_interval (a := 0.41) (b := 0.44) (M := 0.24314)
        ht htq hL (by linarith) hb (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet

theorem first_constraint_rational {L c t : ℝ}
    (h : (c - t ^ 2) * (L - c - 2 * t ^ 2) ≤ 8 * (3 / Real.pi) ^ 2 * t ^ 2) :
    (c - t ^ 2) * (L - c - 2 * t ^ 2) ≤ 8 * t ^ 2 := by
  have hratio : (3 : ℝ) / Real.pi ≤ 1 :=
    (div_le_one Real.pi_pos).mpr Real.pi_gt_three.le
  have hratio0 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
  have hsq : ((3 : ℝ) / Real.pi) ^ 2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
  nlinarith

theorem final_contradiction {c t : ℝ} (ht : 0 < t) (ht12 : t < 0.12)
    (hc : 2.6 * t < c)
    (hdet : (3 / 2 : ℝ) * (c - t ^ 2) ^ 2 ≤ 10 * (3 / Real.pi) ^ 2 * t ^ 2) :
    False := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hratio : (3 : ℝ) / Real.pi < 150 / 157 := by
    rw [div_lt_iff₀ hp]
    nlinarith [Real.pi_gt_d2]
  have hratio0 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
  have hratio2 : ((3 : ℝ) / Real.pi) ^ 2 < (150 / 157 : ℝ) ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have htop := mul_lt_mul_of_pos_right hratio2 ht2
  have hc' : (2.48 : ℝ) * t < c - t ^ 2 := by nlinarith
  have hcsq : ((2.48 : ℝ) * t) ^ 2 < (c - t ^ 2) ^ 2 := by nlinarith
  nlinarith

theorem charge_concave {A : ℝ} (hA : 0.15 ≤ A) :
    ConcaveOn ℝ Set.univ (charge A) := by
  have hlin : ConcaveOn ℝ (Set.univ : Set ℝ) (fun u : ℝ => (0.415 : ℝ) * u) :=
    (concaveOn_id convex_univ).smul (by norm_num)
  have hquad : ConvexOn ℝ (Set.univ : Set ℝ) (fun u : ℝ => (A - 0.15) * u ^ 2) :=
    (Even.convexOn_pow (by decide : Even (2 : ℕ))).smul (by linarith)
  exact hlin.sub hquad

theorem min_charge_le {A a b u : ℝ} (hA : 0.15 ≤ A)
    (ha : a ≤ u) (hb : u ≤ b) : min (charge A a) (charge A b) ≤ charge A u :=
  (charge_concave hA).min_le_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ⟨ha, hb⟩

theorem finalBudget_concave {A k : ℝ} (hA : 0.15 ≤ A) (hk : 0 ≤ k) :
    ConcaveOn ℝ (Set.Ici 0) (finalBudget A k) := by
  have hsqrt : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ =>
      (0.415 * Real.sqrt 2.6) * Real.sqrt t) :=
    Real.strictConcaveOn_sqrt.concaveOn.smul (by positivity)
  have hlin : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => (2.6 * (A - 0.15)) * t) :=
    (convexOn_id (convex_Ici (0 : ℝ))).smul (by positivity)
  have hquad := ((charge_concave hA).subset (Set.subset_univ _) (convex_Ici 0)).smul hk
  have heq : Set.EqOn
      (fun t : ℝ => (0.415 * Real.sqrt 2.6) * Real.sqrt t -
        (2.6 * (A - 0.15)) * t + k * charge A t)
      (finalBudget A k) (Set.Ici 0) := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hsq := Real.sq_sqrt (show 0 ≤ 2.6 * t by positivity)
    dsimp [finalBudget, charge]
    rw [hsq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2.6)]
    ring
  exact ((hsqrt.sub hlin).add hquad).congr heq

theorem clipped_charge {A s q u δ : ℝ} (hd : 0 < A - 0.15) (hs : 0 < s)
    (hq : 0 ≤ q) (hqu : q ≤ u) (hds : (A - 0.15) * s = 0.415)
    (hδ0 : 0 ≤ δ) (hδ : charge A u ≤ δ) :
    (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2) ≤ δ := by
  have hden : 0 < s + q := by positivity
  have hcoef : 0 ≤ (A - 0.15) * q / (s + q) := by positivity
  by_cases hu : s ≤ u
  · have hsq : s ^ 2 - u ^ 2 ≤ 0 := by nlinarith
    exact (mul_nonpos_of_nonneg_of_nonpos hcoef hsq).trans hδ0
  · have hu' : u ≤ s := le_of_lt (lt_of_not_ge hu)
    have hprod : 0 ≤ (A - 0.15) * s * ((s - u) * (u - q)) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hqu))
    have hdiff : 0 ≤ charge A u -
        (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2) := by
      have heq : (charge A u - (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2)) *
          (s + q) = (A - 0.15) * s * ((s - u) * (u - q)) := by
        dsimp [charge]
        rw [← hds]
        field_simp
        ring
      exact nonneg_of_mul_nonneg_left (heq.symm ▸ hprod) hden
    linarith

theorem smallRoot_five :
    0.066 < smallRoot 0.929 2 ∧ smallRoot 0.929 2 < 0.109 ∧
    2 * charge 0.929 (smallRoot 0.929 2) = 1 - 0.929 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61607 / 1000000)
  have hnn := Real.sqrt_nonneg (61607 / 1000000 : ℝ)
  norm_num only [smallRoot, charge] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem smallRoot_six :
    0.066 < smallRoot 0.884 3 ∧ smallRoot 0.884 3 < 0.12 ∧
    3 * charge 0.884 (smallRoot 0.884 3) = 1 - 0.884 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 176099 / 3000000)
  have hnn := Real.sqrt_nonneg (176099 / 3000000 : ℝ)
  norm_num only [smallRoot, charge] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem regime_five : Regime 0.929 2 := by
  obtain ⟨hl, hu, he⟩ := smallRoot_five
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 429)
  have hsqrt0 := Real.sqrt_nonneg (429 : ℝ)
  constructor
  · norm_num
  · norm_num
  · norm_num
  · exact hl
  · simpa using hu.trans (by norm_num : (0.109 : ℝ) < 0.12)
  · exact he
  · norm_num [threshold]; nlinarith
  · norm_num; nlinarith
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [clipCoeff, threshold, charge]
  · norm_num [charge]
  · norm_num [finalBudget, charge]
    nlinarith

theorem regime_six : Regime 0.884 3 := by
  obtain ⟨hl, hu, he⟩ := smallRoot_six
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 429)
  have hsqrt0 := Real.sqrt_nonneg (429 : ℝ)
  constructor
  · norm_num
  · norm_num
  · norm_num
  · exact hl
  · exact hu
  · exact he
  · norm_num [threshold]; nlinarith
  · norm_num; nlinarith
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [clipCoeff, threshold, charge]
  · norm_num [charge]
  · norm_num [finalBudget, charge]
    nlinarith

theorem sum_split (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, f i) + (∑ i ∈ Finset.range (m - p), f (p + i)) =
      ∑ i ∈ Finset.range m, f i := by
  rw [← Finset.sum_range_add, Nat.add_sub_of_le hp]

theorem sum_prefix_le (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m)
    (hf : ∀ i < m, 0 ≤ f i) :
    (∑ i ∈ Finset.range p, f i) ≤ ∑ i ∈ Finset.range m, f i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
    (fun i hi _ => hf i (Finset.mem_range.mp hi))

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem radius_le {i j : ℕ} (hj : j < m) (hij : i ≤ j) : D.r j ≤ D.r i :=
  D.ordered (show i ∈ Set.Iio m by exact lt_of_le_of_lt hij hj) hj hij

theorem minimum_le {i : ℕ} (hi : i < m) : D.r (m - 1) ≤ D.r i :=
  D.radius_le (by omega) (by omega)

theorem prefix_norm {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.r i ^ 2) ≤ 1 := by
  simpa [D.norm] using sum_prefix_le (fun i => D.r i ^ 2) hp (fun i _ => sq_nonneg _)

theorem prefix_budget {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) ≤ 1 - A := by
  simpa [D.budget] using sum_prefix_le D.δ hp D.nonneg

theorem first_two_cap (hm : 2 ≤ m) : D.r 0 ^ 2 + D.r 1 ^ 2 ≤ 8 / 9 := by
  have h0 := D.cap 0 (by omega)
  have h1 := D.cap 1 (by omega)
  have hp0 := D.pos 0 (by omega)
  have hp1 := D.pos 1 (by omega)
  nlinarith

theorem third_twice (hm : 3 ≤ m) : 2 * D.r 2 ^ 2 ≤ D.r 0 ^ 2 + D.r 1 ^ 2 := by
  have hp := D.pos 2 (by omega)
  have h0 := D.radius_le (by omega : 2 < m) (by omega : 0 ≤ 2)
  have h1 := D.radius_le (by omega : 2 < m) (by omega : 1 ≤ 2)
  nlinarith

theorem common_charge (hm : 3 ≤ m) (hA : 0.884 ≤ A) :
    (1 - (D.r 0 ^ 2 + D.r 1 ^ 2)) * (0.415 / D.r 2 - 0.734) ≤ 0.116 := by
  let u := D.r 2
  have hu : 0 < u := D.pos 2 (by omega)
  have hterm : ∀ i < m - 2,
      D.r (2 + i) ^ 2 * (0.415 / u - (A - 0.15)) ≤ D.δ (2 + i) := by
    intro i hi
    have hi' : 2 + i < m := by omega
    have hri := D.pos (2 + i) hi'
    have hle : D.r (2 + i) ≤ u := D.radius_le hi' (by omega)
    have hmul : D.r (2 + i) ^ 2 * (0.415 / u) ≤ 0.415 * D.r (2 + i) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hu).mpr
      nlinarith [mul_nonneg (le_of_lt hri) (sub_nonneg.mpr hle)]
    have hlower := D.lower (2 + i) hi'
    dsimp [charge] at hlower
    nlinarith
  have hsum := Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  rw [← Finset.sum_mul] at hsum
  have hn := sum_split (fun i => D.r i ^ 2) (by omega : 2 ≤ m)
  have hb := sum_split D.δ (by omega : 2 ≤ m)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hn hb
  rw [D.norm] at hn
  rw [D.budget] at hb
  have hd0 := D.nonneg 0 (by omega)
  have hd1 := D.nonneg 1 (by omega)
  have hL : 0 ≤ D.r 0 ^ 2 + D.r 1 ^ 2 := by positivity
  have hAdj : 0 ≤ (A - 0.884) * (D.r 0 ^ 2 + D.r 1 ^ 2) := by positivity
  have hns : (∑ i ∈ Finset.range (m - 2), D.r (2 + i) ^ 2) =
      1 - (D.r 0 ^ 2 + D.r 1 ^ 2) := by linarith
  rw [hns] at hsum
  dsimp [u] at hsum
  nlinarith

theorem tail_coarse_cap (hm : 5 ≤ m) {i : ℕ} (hi : i < m) (hi4 : 4 ≤ i) :
    D.r i ≤ 0.45 := by
  have hn := D.prefix_norm (by omega : 5 ≤ m)
  have hp := D.pos i hi
  have h0 := D.radius_le hi (by omega : 0 ≤ i)
  have h1 := D.radius_le hi (by omega : 1 ≤ i)
  have h2 := D.radius_le hi (by omega : 2 ≤ i)
  have h3 := D.radius_le hi (by omega : 3 ≤ i)
  have h4 := D.radius_le hi hi4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hn
  nlinarith

theorem block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    ∑ i ∈ Finset.range q, D.δ (p + i) ≤ 1 - A := by
  have h := D.prefix_budget hpq
  have hs := sum_split D.δ (by omega : p ≤ p + q)
  rw [Nat.add_sub_cancel_left] at hs
  have hn : 0 ≤ ∑ i ∈ Finset.range p, D.δ i :=
    Finset.sum_nonneg (fun i hi => D.nonneg i (by have := Finset.mem_range.mp hi; omega))
  linarith

theorem prefix_block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) +
      (∑ i ∈ Finset.range q, D.δ (p + i)) ≤ 1 - A := by
  rw [← Finset.sum_range_add]
  exact D.prefix_budget hpq

theorem prefix_block_norm {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.r i ^ 2) +
      (∑ i ∈ Finset.range q, D.r (p + i) ^ 2) ≤ 1 := by
  rw [← Finset.sum_range_add]
  exact D.prefix_norm hpq

theorem minimum_lower (hm : 5 ≤ m) (hA : 0.884 ≤ A)
    (hdet : (D.r 2 ^ 2 - D.r (m - 1) ^ 2) *
      (D.r 0 ^ 2 + D.r 1 ^ 2 - D.r 2 ^ 2 - 2 * D.r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2) :
    0.066 < D.r (m - 1) := by
  have hc := D.common_charge (by omega) hA
  have hL := D.first_two_cap (by omega)
  have hu := third_radius_gt (D.pos 2 (by omega)) hL hc
  exact minimum_gt (D.pos (m - 1) (by omega)).le hu hL
    (D.third_twice (by omega)) hc (first_constraint_rational hdet)

theorem tail_base_charge {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi4 : 4 ≤ i) :
    charge A 0.066 ≤ D.δ i := by
  have h := min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    (ht.le.trans (D.minimum_le hi)) (D.tail_coarse_cap hm hi hi4)
  rw [min_eq_left R.tail_end_charge] at h
  exact h.trans (D.lower i hi)

theorem fourth_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) : D.r 3 ≤ 0.42 := by
  by_contra! h4
  have hk : 2 ≤ k := R.k_lower
  have hd : 0 < A - 0.15 := by linarith [R.A_lower]
  have hs : 0 < threshold A := div_pos (by norm_num) hd
  have hds : (A - 0.15) * threshold A = 0.415 := by
    unfold threshold
    field_simp
  have hcoef : 0 ≤ clipCoeff A := by unfold clipCoeff; positivity
  have hfirst : ∀ i < 4,
      clipCoeff A * ((threshold A) ^ 2 - D.r i ^ 2) ≤ D.δ i := by
    intro i hi
    have hi' : i < m := by omega
    exact clipped_charge hd hs (by norm_num)
      (h4.le.trans (D.radius_le (by omega : 3 < m) (by omega)))
      hds (D.nonneg i hi') (D.lower i hi')
  have hf := Finset.sum_le_sum (fun i hi => hfirst i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hf
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] at hf
  have htailnorm : (k - 1 : ℕ) * (0.066 : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range (k - 1), D.r (4 + i) ^ 2 := by
    have hterm : ∀ i < k - 1, (0.066 : ℝ) ^ 2 ≤ D.r (4 + i) ^ 2 := by
      intro i hi
      have hi' : 4 + i < m := by omega
      have hr := ht.trans_le (D.minimum_le hi')
      nlinarith
    simpa using Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hn := D.prefix_block_norm (by omega : 4 + (k - 1) ≤ m)
  have hnm : (∑ i ∈ Finset.range 4, D.r i ^ 2) ≤
      1 - (k - 1 : ℕ) * (0.066 : ℝ) ^ 2 := by linarith
  have hf' := mul_le_mul_of_nonneg_left (sub_le_sub_left hnm (4 * (threshold A) ^ 2)) hcoef
  have htbudget : (k - 1 : ℕ) * charge A 0.066 ≤
      ∑ i ∈ Finset.range (k - 1), D.δ (4 + i) := by
    have hterm : ∀ i < k - 1, charge A 0.066 ≤ D.δ (4 + i) := by
      intro i hi
      exact D.tail_base_charge R hm ht (by omega) (by omega)
    simpa using Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hb := D.prefix_block_budget (by omega : 4 + (k - 1) ≤ m)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast] at hf' htbudget
  have hmarg := R.four_margin
  nlinarith

theorem tail_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    D.r i ≤ 0.42 :=
  (D.radius_le hi hi3).trans (D.fourth_cap R hm hkm ht)

theorem minimum_charge_bound {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    (k : ℝ) * charge A (D.r (m - 1)) ≤ 1 - A := by
  have hterm : ∀ i < k,
      min (charge A (D.r (m - 1))) (charge A 0.42) ≤ D.δ (3 + i) := by
    intro i hi
    have hi' : 3 + i < m := by omega
    exact (min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
      (D.minimum_le hi') (D.tail_cap R hm hkm ht hi' (by omega))).trans (D.lower _ hi')
  have hs := Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hb := D.block_budget hkm
  by_cases h : charge A (D.r (m - 1)) ≤ charge A 0.42
  · rw [min_eq_left h] at hs
    exact hs.trans hb
  · rw [min_eq_right (le_of_not_ge h)] at hs
    linarith [R.cap_charge]

theorem minimum_le_root {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    D.r (m - 1) ≤ smallRoot A k := by
  have hb := D.minimum_charge_bound R hm hkm ht
  have hcap := D.tail_cap R hm hkm ht (by omega : m - 1 < m) (by omega : 3 ≤ m - 1)
  have hd : 0 ≤ A - 0.15 := by linarith [R.A_lower]
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) R.k_lower)
  by_contra! h
  have hslope : 0 < 0.415 - (A - 0.15) * (D.r (m - 1) + smallRoot A k) := by
    have hmul := mul_le_mul_of_nonneg_left hcap hd
    linarith [R.root_slope]
  have hprod := mul_pos (sub_pos.mpr h) hslope
  have hcharge : charge A (smallRoot A k) < charge A (D.r (m - 1)) := by
    dsimp [charge]
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hcharge hk
  linarith [R.root_eq]

theorem tail_charge {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    charge A (D.r (m - 1)) ≤ D.δ i := by
  have hbudget := D.minimum_charge_bound R hm hkm ht
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) R.k_lower)
  have hcharge : charge A (D.r (m - 1)) ≤ charge A 0.42 := by
    have h := (lt_of_le_of_lt hbudget R.cap_charge)
    nlinarith
  have h := min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    (D.minimum_le hi) (D.tail_cap R hm hkm ht hi hi3)
  rw [min_eq_left hcharge] at h
  exact h.trans (D.lower i hi)

theorem third_large {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) : 2.6 * D.r (m - 1) < D.r 2 ^ 2 := by
  let t := D.r (m - 1)
  let t₀ := smallRoot A k
  have ht0 : 0 < t := by dsimp [t]; linarith
  have htroot : t ≤ t₀ := D.minimum_le_root R hm hkm ht
  have htrootpos : 0 < t₀ := by dsimp [t₀]; linarith [R.root_lower]
  have hd : 0 < A - 0.15 := by linarith [R.A_lower]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htlt : t₀ < 0.12 := R.root_upper
  have he_inc : charge A 0.066 ≤ charge A t := by
    have hmul := mul_le_mul_of_nonneg_left (show 0.066 + t ≤ 0.42 + t₀ by linarith) hd.le
    have hslope : 0 ≤ 0.415 - (A - 0.15) * (t + 0.066) := by
      linarith [R.root_slope]
    have hprod := mul_nonneg (show 0 ≤ t - 0.066 by dsimp [t]; linarith) hslope
    dsimp [charge]
    nlinarith
  have hfst : 1 - A < charge A 0.23 + (k : ℝ) * charge A t := by
    have hm := mul_le_mul_of_nonneg_left he_inc hk
    linarith [R.third_margin]
  have hspos : 0 < threshold A := div_pos (by norm_num) hd
  have hslopeeq : (A - 0.15) * threshold A = 0.415 := by
    unfold threshold
    field_simp
  have hsqrtpos : 0 < Real.sqrt (2.6 * t₀) := Real.sqrt_pos.mpr (by positivity)
  have hsqrtsq := Real.sq_sqrt (show 0 ≤ 2.6 * t₀ by positivity)
  have hsqrtlt : Real.sqrt (2.6 * t₀) < threshold A := by
    have hcap := R.root_cap
    dsimp [t₀] at hsqrtsq ⊢
    nlinarith
  have hepos : 0 < charge A (Real.sqrt (2.6 * t₀)) := by
    have hp := mul_pos hd (sub_pos.mpr hsqrtlt)
    have hp' := mul_pos hsqrtpos hp
    dsimp [charge]
    nlinarith
  have hend : 1 - A < finalBudget A k t₀ := by
    dsimp [finalBudget]
    linarith [R.root_eq]
  have hlower := (finalBudget_concave (by linarith [R.A_lower] : 0.15 ≤ A) hk).min_le_of_mem_Icc (by norm_num : (0.066 : ℝ) ∈ Set.Ici 0)
      (show t₀ ∈ Set.Ici 0 by exact htrootpos.le) (show t ∈ Set.Icc 0.066 t₀ by exact ⟨ht.le, htroot⟩)
  have hsnd : 1 - A < finalBudget A k t :=
    lt_of_lt_of_le (lt_min R.final_margin hend) hlower
  by_contra! hthird
  have hthirdpos := D.pos 2 (by omega)
  have hthirdlow := third_radius_gt hthirdpos (D.first_two_cap (by omega))
    (D.common_charge (by omega) R.A_lower)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2.6 * t by positivity)
  have hthirdhi : D.r 2 ≤ Real.sqrt (2.6 * t) := by
    nlinarith [Real.sqrt_nonneg (2.6 * t)]
  have hthirdcharge := (min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    hthirdlow.le hthirdhi).trans (D.lower 2 (by omega))
  have htailterm : ∀ i < k, charge A t ≤ D.δ (3 + i) := by
    intro i hi
    exact D.tail_charge R hm hkm ht (by omega) (by omega)
  have htail := Finset.sum_le_sum (fun i hi => htailterm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htail
  have hb := D.prefix_block_budget hkm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hb
  have h0 := D.nonneg 0 (by omega)
  have h1 := D.nonneg 1 (by omega)
  dsimp [finalBudget] at hsnd
  rcases le_total (charge A 0.23) (charge A (Real.sqrt (2.6 * t))) with h | h
  · rw [min_eq_left h] at hthirdcharge
    linarith
  · rw [min_eq_right h] at hthirdcharge
    linarith

theorem incompatible {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (hdet₁ : (D.r 2 ^ 2 - D.r (m - 1) ^ 2) *
      (D.r 0 ^ 2 + D.r 1 ^ 2 - D.r 2 ^ 2 - 2 * D.r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (D.r 2 ^ 2 - D.r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2) : False := by
  have ht := D.minimum_lower hm R.A_lower hdet₁
  have htroot := D.minimum_le_root R hm hkm ht
  have ht12 := lt_of_le_of_lt htroot R.root_upper
  exact final_contradiction (by linarith : 0 < D.r (m - 1)) ht12
    (D.third_large R hm hkm ht) hdet₂

end RadiusData

theorem scalar_incompatibility {m : ℕ} (hm : 5 ≤ m) (r P : ℕ → ℝ)
    (hpos : ∀ i < m, 0 < r i) (hordered : AntitoneOn r (Set.Iio m))
    (hcap : ∀ i < m, r i ≤ 2 / 3)
    (hnorm : ∑ i ∈ Finset.range m, r i ^ 2 = 1)
    (hprob : ∑ i ∈ Finset.range m, P i = 1)
    (hquad : ∀ i < m, (if m = 5 then (0.929 : ℝ) else 0.884) * r i ^ 2 ≤ P i)
    (hlin : ∀ i < m, 0.415 * r i + 0.15 * r i ^ 2 ≤ P i)
    (hdet₁ : (r 2 ^ 2 - r (m - 1) ^ 2) *
      (r 0 ^ 2 + r 1 ^ 2 - r 2 ^ 2 - 2 * r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (r 2 ^ 2 - r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2) : False := by
  let A : ℝ := if m = 5 then 0.929 else 0.884
  let D : RadiusData m A := {
    r := r
    δ := fun i => P i - A * r i ^ 2
    pos := hpos
    ordered := hordered
    cap := hcap
    norm := hnorm
    nonneg := fun i hi => sub_nonneg.mpr (hquad i hi)
    lower := by intro i hi; dsimp [charge]; linarith [hlin i hi]
    budget := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, hprob, mul_one] }
  by_cases hm5 : m = 5
  · have hR : Regime A 2 := by simpa [A, hm5] using regime_five
    exact D.incompatible hR hm (by omega) hdet₁ hdet₂
  · have hR : Regime A 3 := by simpa [A, hm5] using regime_six
    exact D.incompatible hR hm (by omega) hdet₁ hdet₂

end Scalar

end GaussianPropeller

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Elimination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction.Configuration
variable {d k:ℕ}

lemma impossible_five_or_more (D:Configuration d k) (hk:5≤k) : False := by
  classical
  let r:ℕ→ℝ := fun i=>if hi:i<k then ‖D.z ⟨i,hi⟩‖ else 0
  let P:ℕ→ℝ := fun i=>if hi:i<k then D.P ⟨i,hi⟩ else 0
  have hr:∀ i:Fin k,r i=‖D.z i‖ := by intro i; simp [r,i.isLt]
  have hp:∀ i:Fin k,P i=D.P i := by intro i; simp [P,i.isLt]
  have hnorm:∑ i∈Finset.range k,r i^2=1 := by
    rw [Finset.sum_range]
    simpa only [hr] using D.norm
  have hprob:∑ i∈Finset.range k,P i=1 := by
    rw [Finset.sum_range]
    simpa only [hp] using D.probability
  let i:Fin k:=⟨k-1,by omega⟩
  let j:Fin k:=⟨0,by omega⟩
  let l:Fin k:=⟨1,by omega⟩
  let q:Fin k:=⟨2,by omega⟩
  have hdet:=configuration_determinants D.z D.zero D.obtuse i (D.pos i)
    (j:=j) (l:=l) (q:=q) (by dsimp [i,j]; intro h; have:=congrArg Fin.val h; simp at this; omega)
    (by dsimp [i,l]; intro h; have:=congrArg Fin.val h; simp at this; omega)
    (by dsimp [i,q]; intro h; have:=congrArg Fin.val h; simp at this; omega)
    (by simp [j,l,Fin.ext_iff]) (by simp [j,q,Fin.ext_iff]) (by simp [l,q,Fin.ext_iff])
    (D.order (by simp [j,q])) (D.order (by simp [l,q]))
    (D.order (by change 2≤k-1; omega)) (D.pair i)
  apply Scalar.scalar_incompatibility hk r P
  · intro a ha
    simp only [r,dite_eq_left ha]
    exact norm_pos_iff.mpr (D.pos _)
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only [r,dite_eq_left ha,dite_eq_left hb]
    exact D.order (show (⟨a,ha⟩:Fin k)≤⟨b,hb⟩ from hab)
  · intro a ha
    simpa only [r,dite_eq_left ha] using D.cap ⟨a,ha⟩
  · exact hnorm
  · exact hprob
  · intro a ha
    simpa only [r,P,dite_eq_left ha] using D.quadratic ⟨a,ha⟩
  · intro a ha
    simpa only [r,P,dite_eq_left ha] using D.linear ⟨a,ha⟩
  · simpa only [r,dite_eq_left (show 0<k by omega),dite_eq_left (show 1<k by omega),
      dite_eq_left (show 2<k by omega),dite_eq_left (show k-1<k by omega),i,j,l,q] using hdet.1
  · simpa only [r,dite_eq_left (show 2<k by omega),dite_eq_left (show k-1<k by omega),i,q] using hdet.2

end GaussianPropeller.Reduction.Configuration

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

lemma remove_null_partition {A:Fin (k+1)→Set (Space d)} (hA:IsPartition A)
    (i:Fin (k+1)) (hi:gaussian d (A i)=0) :
    IsPartition (fun j:Fin k=>A (i.succAbove j)) := by
  constructor
  · intro j; exact hA.1 _
  have hn:∀ᵐ x∂gaussian d,x∉A i := by
    exact (ae_iff.mpr (by simpa using hi))
  filter_upwards [hA.2,hn] with x hx hxi
  obtain ⟨j,hj,huniq⟩:=hx
  have hji:j≠i := by intro hh; subst j; contradiction
  obtain ⟨a,ha⟩:=Fin.exists_succAbove_eq hji
  refine ⟨a,?_,?_⟩
  · simpa only [ha] using hj
  · intro b hb
    apply Fin.succAbove_right_injective
    exact (huniq _ hb).trans ha.symm

lemma remove_null_value {A:Fin (k+1)→Set (Space d)} (i:Fin (k+1))
    (hi:gaussian d (A i)=0) : value (fun j:Fin k=>A (i.succAbove j))=value A := by
  unfold value
  rw [Fin.sum_univ_succAbove (fun j=>‖centroid (A j)‖^2) i,centroid_eq_zero_of_null hi]
  simp

lemma partition_bound_small {A:Fin k→Set (Space d)} (hk:k≤3) (hA:IsPartition A) :
    value A≤9/(8*Real.pi) := by
  have he:∃ B:Fin 3→Set (Space d), IsPartition B ∧ value B=value A := by
    have hc:∀ m, k ≤ m → ∃ B:Fin m→Set (Space d), IsPartition B ∧ value B=value A := by
      intro m hm
      induction m,hm using Nat.le_induction with
      | base => exact ⟨A,hA,rfl⟩
      | succ m hm ih =>
        obtain ⟨B,hB,hv⟩:=ih
        let B' : Fin (m+1) → Set (Space d) := Fin.lastCases ∅ B
        have hp : IsPartition B' := append_empty_partition (A := B) hB
        have he : value B' = value B := append_empty_value B
        exact ⟨B',hp,he.trans hv⟩
    exact hc 3 hk
  obtain ⟨B,hB,hv⟩:=he
  rw [←hv]
  exact three_partition_bound hB

end GaussianPropeller.Reduction

end OAI
end

section
-- module Solutions.OAIQW_GaussianPropeller.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction

theorem all_partition_bound (d:ℕ) (hd:0<d) :
    ∀ k (A:Fin k→Set (Space d)), IsPartition A → value A≤9/(8*Real.pi) := by
  classical
  let : NeZero d := ⟨by omega⟩
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A hA
    by_cases hk:k≤3
    · exact partition_bound_small hk hA
    let : NeZero k := ⟨by omega⟩
    obtain ⟨B,hB⟩:=exists_minimal_optimal (d:=d) (k:=k)
    suffices hb:value B≤9/(8*Real.pi) from (hB.1.2 _ hA).trans hb
    by_contra hn
    have hC:9/(8*Real.pi)<value B := lt_of_not_ge hn
    by_cases hall:∀ j,gaussian d (B j)≠0
    · obtain ⟨D⟩:=exists_configuration (by omega) hB hC hall
      by_cases hk4:k=4
      · subst k
        exact D.impossible_four
      · exact D.impossible_five_or_more (by omega)
    · push Not at hall
      obtain ⟨i,hi⟩:=hall
      cases k with
      | zero => omega
      | succ m =>
        have hp:=remove_null_partition hB.1.1 i hi
        have hv:=ih m (by omega) (fun j=>B (i.succAbove j)) hp
        rw [remove_null_value i hi] at hv
        exact (not_le_of_gt hC) hv

end GaussianPropeller.Reduction

namespace GaussianPropeller

theorem all_partitions_oai : AllPartitions := by
  constructor
  · intro d k hd hk A hA
    exact Reduction.all_partition_bound d hd k A hA
  · exact Reduction.propeller_attainment

end GaussianPropeller

end OAI
end

theorem solution : type_of% @OAI.GaussianPropeller.all_partitions_oai := @OAI.GaussianPropeller.all_partitions_oai
