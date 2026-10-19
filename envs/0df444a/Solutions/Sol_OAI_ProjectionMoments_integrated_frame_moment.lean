-- Prove2me | solution 1 for OAI.ProjectionMoments.integrated_frame_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:34:57.741999+00:00
-- url     : https://prove2.me/submissions/f6f5f07c-e4b4-4fd0-ac84-4576987cdbda

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/FrameMoments.lean:L270-L310
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.integrated_frame_moment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Theorems.Thm_OAI_NoiselessRegression_ae_pi_snoc
import Theorems.Thm_OAI_NoiselessRegression_card_le_volume_ratio
import Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound
import Theorems.Thm_OAI_NoiselessRegression_replicaConstant_le
import Theorems.Thm_OAI_ProjectionMoments_ballAverage_eq
import Theorems.Thm_OAI_ProjectionMoments_ballKernel_integral
import Theorems.Thm_OAI_ProjectionMoments_frame_cost_power
import Theorems.Thm_OAI_ProjectionMoments_frame_gaussian_comparison
import Theorems.Thm_OAI_ProjectionMoments_gaussian_graph_kernel_bound
import Theorems.Thm_OAI_ProjectionMoments_lowerDensity_is_density
import Theorems.Thm_OAI_ProjectionMoments_normalizedRescale_support

-- ---- from OAI.Probability.GaussianRegression.Nets ----
namespace OAI

/-!
Local mass bounds and quantitative finite Euclidean nets.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u

namespace NoiselessRegression

section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in

theorem HasLocalMassBound.any_center {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (z : E) {r : ℝ} (hr : 0 < r) :
    ν (Metric.closedBall z r) ≤ ENNReal.ofReal ((2 * r) ^ a) := by
  by_cases hmass : ν (Metric.closedBall z r) = 0
  · simp [hmass]
  obtain ⟨t, htball, htsupp⟩ := ν.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hmass)
  refine (measure_mono ?_).trans (hν t htsupp (2 * r) (by positivity))
  intro x hx
  apply Metric.mem_closedBall.mpr
  calc
    dist x t ≤ dist x z + dist z t := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (Metric.mem_closedBall.mp hx)
      (by simpa [dist_comm] using Metric.mem_closedBall.mp htball)
    _ = 2 * r := by ring

end FrostmanGeometry

section FiniteNets

variable {E : Type*} [PseudoMetricSpace E]

end FiniteNets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_unit_ball_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E ∧
      ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ r := by
  classical
  have hbound : ∀ s : Finset E, (∀ x ∈ s, ‖x‖ ≤ 1) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r < dist x y) →
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ E := by
    intro s hs hsep
    refine (card_le_volume_ratio s hr zero_le_one hs
      (fun x hx y hy hne => (hsep x hx y hy hne).le)).trans ?_
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_div_iff₀ (by positivity : 0 < r / 2) hr).mpr
    nlinarith
  obtain ⟨s, hs, hsep, hnet⟩ := exists_net_of_finite_packing_bound
    {x : E | ‖x‖ ≤ 1} hr.le ⌈(3 / r) ^ Module.finrank ℝ E⌉₊
    (by
      intro s hs hsep
      exact_mod_cast (hbound s hs hsep).trans (Nat.le_ceil _))
  exact ⟨s, hs, hbound s hs hsep, hnet⟩

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.InverseMoments ----
namespace OAI

/-!
Inverse moments from polynomial tube bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u

namespace NoiselessRegression

section InverseMoments

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma inverse_pow_dyadic_majorant (f : X → ℝ) (m : ℕ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      1 + ∑' k : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
  classical
  by_cases hzero : f x = 0
  · simp only [hzero, inv_zero]
    exact le_add_of_le_left (by cases m <;> simp)
  have hxpos : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hzero)
  by_cases hxone : 1 ≤ f x
  · apply le_add_of_le_left
    have h : (f x)⁻¹ ^ m ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr (hf x)) (inv_le_one_of_one_le₀ hxone)
    simpa using ENNReal.ofReal_le_ofReal h
  obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hxpos
    (le_of_not_ge hxone) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hinv : (f x)⁻¹ ≤ (2 : ℝ) ^ (k + 1) := by
    have h := (inv_le_inv₀ hxpos (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) _)).2 hklo.le
    simpa using h
  have hpow : ENNReal.ofReal ((f x)⁻¹ ^ m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := by
    apply ENNReal.ofReal_le_ofReal
    simpa [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (inv_nonneg.mpr (hf x)) hinv m
  calc
    ENNReal.ofReal ((f x)⁻¹ ^ m) ≤ ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) := hpow
    _ = ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1)))) x := by
      rw [Set.indicator_of_mem (show x ∈ {x | f x ≤ (1 / 2 : ℝ) ^ k} from hkhi)]
    _ ≤ ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x :=
      ENNReal.le_tsum (f := fun j => ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x) k
    _ ≤ 1 + ∑' j : ℕ, ({x | f x ≤ (1 / 2 : ℝ) ^ j}).indicator
        (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (j + 1)))) x := le_add_left le_rfl

lemma dyadic_power_cancel (m k : ℕ) :
    (2 : ℝ) ^ (m * (k + 1)) * ((1 / 2 : ℝ) ^ k) ^ (m + 1) =
      (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k := by
  rw [Nat.mul_add, mul_one, pow_add, pow_succ]
  have h : (2 : ℝ) ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m = 1 := by
    rw [Nat.mul_comm m k, pow_mul, ← mul_pow, ← mul_pow]
    norm_num
  calc
    2 ^ (m * k) * 2 ^ m * (((1 / 2 : ℝ) ^ k) ^ m * (1 / 2 : ℝ) ^ k) =
      (2 ^ (m * k) * ((1 / 2 : ℝ) ^ k) ^ m) * (2 ^ m * (1 / 2 : ℝ) ^ k) := by ring
    _ = _ := by rw [h, one_mul]

theorem inverse_moment_of_tube_bound (μ : Measure X) (f : X → ℝ) (m : ℕ)
    (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ {x | f x ≤ r} ≤ C * ENNReal.ofReal (r ^ (m + 1))) :
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤
      μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
  classical
  let g : ℕ → X → ℝ≥0∞ := fun k =>
    ({x | f x ≤ (1 / 2 : ℝ) ^ k}).indicator
      (fun _ => ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))))
  have hg : ∀ k, Measurable (g k) := fun k =>
    measurable_const.indicator (measurableSet_le hf measurable_const)
  calc
    ∫⁻ x, ENNReal.ofReal ((f x)⁻¹ ^ m) ∂μ ≤ ∫⁻ x, 1 + ∑' k, g k x ∂μ :=
      lintegral_mono (inverse_pow_dyadic_majorant f m hnonneg)
    _ = μ Set.univ + ∑' k, ∫⁻ x, g k x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul, lintegral_tsum (fun k => (hg k).aemeasurable)]
    _ ≤ μ Set.univ + ∑' k, C * ENNReal.ofReal ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ k) := by
      apply add_le_add le_rfl
      apply ENNReal.tsum_le_tsum
      intro k
      dsimp only [g]
      rw [lintegral_indicator (measurableSet_le hf measurable_const), lintegral_const,
        Measure.restrict_apply_univ]
      calc
        ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) * μ {x | f x ≤ (1 / 2 : ℝ) ^ k} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (m * (k + 1))) *
              (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ (m + 1))) := by
          gcongr
          exact htube _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
        _ = _ := by
          rw [← mul_assoc, mul_comm _ C, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            dyadic_power_cancel]
    _ = μ Set.univ + C * (2 : ℝ≥0∞) ^ (m + 1) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ m),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num [pow_succ, mul_assoc, ENNReal.ofReal_div_of_pos]

end InverseMoments

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.AffineTubes ----
namespace OAI

/-!
Affine tube covers and inverse-distance bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u

namespace NoiselessRegression

section AffineTubes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open EuclideanGeometry

theorem exists_affine_tube_cover (L : AffineSubspace ℝ E) [Nonempty L]
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset L.direction,
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ L.direction ∧
      ∀ t : E, ‖t‖ ≤ 1 → Metric.infDist t L ≤ r →
        ∃ y ∈ s, dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤ 2 * r := by
  classical
  obtain ⟨s, _, hcard, hnet⟩ := exists_unit_ball_net (E := L.direction) hr hr1
  refine ⟨s, hcard, ?_⟩
  intro t ht hdist
  obtain ⟨y, hy, hty⟩ := hnet (L.direction.orthogonalProjectionOnto t)
    ((L.direction.norm_orthogonalProjectionOnto_apply_le t).trans ht)
  refine ⟨y, hy, ?_⟩
  have hproj : (orthogonalProjection L t : E) =
      (L.direction.orthogonalProjectionOnto t : E) + (orthogonalProjection L 0 : E) := by
    have h := (orthogonalProjection L).map_vadd (0 : E) t
    simpa only [vadd_eq_add, add_zero, orthogonalProjection_contLinear,
      AffineSubspace.coe_vadd] using congrArg (fun x : L => (x : E)) h
  have hpdist : dist (orthogonalProjection L t : E)
      ((y : E) + (orthogonalProjection L 0 : E)) ≤ r := by
    rw [hproj, dist_add_right]
    exact hty
  have hd : dist t (orthogonalProjection L t : E) ≤ r := by
    rwa [dist_orthogonalProjection_eq_infDist]
  calc
    dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤
        dist t (orthogonalProjection L t : E) +
          dist (orthogonalProjection L t : E) ((y : E) + (orthogonalProjection L 0 : E)) :=
      dist_triangle _ _ _
    _ ≤ r + r := add_le_add hd hpdist
    _ = 2 * r := by ring

theorem HasLocalMassBound.affine_tube {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction * (4 * r) ^ a) := by
  classical
  obtain ⟨s, hcard, hcover⟩ := exists_affine_tube_cover L hr hr1
  let c : L.direction → E := fun y => (y : E) + (orthogonalProjection L 0 : E)
  have hsub : {t | Metric.infDist t L ≤ r} ≤ᵐ[ν]
      ⋃ y ∈ s, Metric.closedBall (c y) (2 * r) := by
    filter_upwards [ν.support_mem_ae] with t ht
    intro hdist
    have htunit : ‖t‖ ≤ 1 := by simpa using hsupport ht
    obtain ⟨y, hy, hty⟩ := hcover t htunit hdist
    exact mem_iUnion₂.mpr ⟨y, hy, hty⟩
  calc
    ν {t | Metric.infDist t L ≤ r} ≤ ν (⋃ y ∈ s, Metric.closedBall (c y) (2 * r)) :=
      measure_mono_ae hsub
    _ ≤ ∑ y ∈ s, ν (Metric.closedBall (c y) (2 * r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ s, ENNReal.ofReal ((4 * r) ^ a) := by
      refine Finset.sum_le_sum fun y _ => ?_
      simpa only [show (2 : ℝ) * (2 * r) = 4 * r by ring] using
        hν.any_center (c y) (r := 2 * r) (by positivity)
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal ((4 * r) ^ a) := by simp
    _ ≤ ENNReal.ofReal ((3 / r) ^ Module.finrank ℝ L.direction) *
        ENNReal.ofReal ((4 * r) ^ a) := by
      gcongr
      exact_mod_cast ENNReal.ofReal_le_ofReal hcard
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

lemma tube_radius_factors (ℓ : ℕ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (3 / r) ^ ℓ * (4 * r) ^ a =
      (3 : ℝ) ^ ℓ * (4 : ℝ) ^ a * r ^ (a - ℓ) := by
  rw [div_pow, Real.mul_rpow (by norm_num) hr.le,
    Real.rpow_sub_natCast hr.ne']
  ring

theorem HasLocalMassBound.affine_tube_pow {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (k : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + k ≤ a)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ν {t | Metric.infDist t L ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
        ENNReal.ofReal (r ^ k) := by
  refine (hν.affine_tube hsupport L hr hr1).trans ?_
  rw [tube_radius_factors _ _ hr, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)

theorem HasLocalMassBound.affine_inverse_moment {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ t, ENNReal.ofReal ((Metric.infDist t L)⁻¹ ^ m) ∂ν ≤
      ν Set.univ +
        ENNReal.ofReal ((3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a) *
          (2 : ℝ≥0∞) ^ (m + 1) := by
  apply inverse_moment_of_tube_bound ν _ m (Metric.continuous_infDist_pt _).measurable
    (fun _ => Metric.infDist_nonneg)
  intro r hr hr1
  exact hν.affine_tube_pow hsupport L (m + 1) hmargin hr hr1

theorem HasLocalMassBound.affine_null {ν : Measure E} {a : ℝ}
    (hν : HasLocalMassBound ν a) (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L]
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + 1 ≤ a) : ν L = 0 := by
  let C : ℝ := (3 : ℝ) ^ Module.finrank ℝ L.direction * (4 : ℝ) ^ a
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (n : ℕ) : ν L ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n) := by
    have hn : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hn1 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      ν L ≤ ν {t | Metric.infDist t L ≤ (1 / 2 : ℝ) ^ n} := by
        apply measure_mono
        intro t ht
        simp only [mem_ofPred_eq, Metric.infDist_zero_of_mem ht]
        exact hn.le
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ 1) :=
        hν.affine_tube_pow hsupport L 1 (by simpa using hmargin) hn hn1
      _ = _ := by rw [pow_one, ENNReal.ofReal_mul hC]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (C * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))) using 1
    simp
  exact le_antisymm (ge_of_tendsto' hlim hb) (by positivity)

end AffineTubes

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Gram ----
namespace OAI

/-!
Gram determinants, orthogonal distances, and product integration.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]
lemma gram_linear_combination (w : ι → E) (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, (T i j) • w i) =
      T.transpose * Matrix.gram ℝ w * T := by
  ext a b
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  congr 1
  ext j
  congr 1
  ext i
  ring

variable (n : ℕ)
lemma gsUpper_expansion (v : Fin n → E) (j : Fin n) :
    ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i = v j := by
  simp only [gsUpper, add_smul, Finset.sum_add_distrib]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs => rw [gramSchmidt_def'' ℝ v j]
  congr 1
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

lemma gsUpper_det (v : Fin n → E) : (gsUpper n v).det = 1 := by
  have htri : (gsUpper n v).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [gsUpper, (ne_of_gt hij), (not_lt_of_ge hij.le)]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gsUpper]

lemma gram_gramSchmidt_diagonal (v : Fin n → E) :
    Matrix.gram ℝ (gramSchmidt ℝ v) = Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.gram_apply]
  · simp [Matrix.gram_apply, hij,
      gramSchmidt_orthogonal ℝ v hij]

theorem det_gram_eq_prod_gramSchmidt (v : Fin n → E) :
    (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hv : (fun j => ∑ i, (gsUpper n v i j) • gramSchmidt ℝ v i) = v :=
    funext (gsUpper_expansion n v)
  have h := gram_linear_combination (gramSchmidt ℝ v) (gsUpper n v)
  rw [hv] at h
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, gsUpper_det,
    one_mul, mul_one, gram_gramSchmidt_diagonal, Matrix.det_diagonal]
end GramFactorization

section GramDistances
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}
omit [FiniteDimensional ℝ E] in
lemma sub_gramSchmidt_mem_span (v : Fin n → E) (j : Fin n) :
    v j - gramSchmidt ℝ v j ∈ Submodule.span ℝ (v '' Set.Iio j) := by
  rw [← span_gramSchmidt_Iio ℝ v j]
  conv => arg 2; lhs; rw [gramSchmidt_def'' ℝ v j]
  rw [add_sub_cancel_left]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

omit [FiniteDimensional ℝ E] in
lemma gramSchmidt_mem_span_orthogonal (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j ∈ (Submodule.span ℝ (v '' Set.Iio j))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    exact gramSchmidt_inv_triangular ℝ v hi
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

lemma gramSchmidt_eq_sub_starProjection (v : Fin n → E) (j : Fin n) :
    gramSchmidt ℝ v j = v j -
      (Submodule.span ℝ (v '' Set.Iio j)).starProjection (v j) := by
  have h := (Submodule.span ℝ (v '' Set.Iio j)).eq_starProjection_of_mem_orthogonal
    (u := v j) (sub_gramSchmidt_mem_span v j)
    (by simpa using gramSchmidt_mem_span_orthogonal v j)
  rw [h, sub_sub_cancel]

lemma norm_gramSchmidt_eq_infDist (v : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ v j‖ = Metric.infDist (v j)
      (Submodule.span ℝ (v '' Set.Iio j) : Set E) := by
  rw [gramSchmidt_eq_sub_starProjection, Submodule.starProjection_minimal,
    Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl
lemma infDist_affine_mk' (p x : E) (K : Submodule ℝ E) :
    Metric.infDist x (AffineSubspace.mk' p K : Set E) =
      Metric.infDist (x - p) (K : Set E) := by
  rw [← EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    EuclideanGeometry.orthogonalProjection_apply_mem _ (AffineSubspace.self_mem_mk' p K),
    dist_eq_norm, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  change ‖x - _‖ = ⨅ y : K, ‖(x - p) - y‖
  rw [← Submodule.starProjection_minimal]
  simp only [AffineSubspace.direction_mk', vsub_eq_sub, vadd_eq_add,
    Submodule.coe_orthogonalProjectionOnto_apply]
  congr 1
  abel

lemma norm_gramSchmidt_sub_eq_affine_infDist (p : E) (t : Fin n → E) (j : Fin n) :
    ‖gramSchmidt ℝ (fun i => t i - p) j‖ =
      Metric.infDist (t j) (AffineSubspace.mk' p
        (Submodule.span ℝ ((fun i => t i - p) '' Set.Iio j)) : Set E) := by
  rw [infDist_affine_mk', norm_gramSchmidt_eq_infDist]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    v '' Set.Iio j.castSucc = (fun i => v i.castSucc) '' Set.Iio j := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i.val < n := lt_trans hi j.isLt
    exact ⟨⟨i.val, hin⟩, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.castSucc, hi, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma image_Iio_last (v : Fin (n+1) → E) :
    v '' Set.Iio (Fin.last n) = Set.range (fun i : Fin n => v i.castSucc) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i.val, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩

lemma gramSchmidt_castSucc (v : Fin (n+1) → E) (j : Fin n) :
    gramSchmidt ℝ v j.castSucc = gramSchmidt ℝ (fun i => v i.castSucc) j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    image_Iio_castSucc]

variable [MeasurableSpace E] [BorelSpace E]
lemma measurable_gramSchmidt (j : Fin n) :
    Measurable (fun v : Fin n → E => gramSchmidt ℝ v j) := by
  refine (wellFounded_lt : WellFounded ((· < ·) : Fin n → Fin n → Prop)).induction
    (C := fun j : Fin n => Measurable (fun v : Fin n → E => gramSchmidt ℝ v j)) j ?_
  intro j ih
  have heq : (fun v : Fin n → E => gramSchmidt ℝ v j) =
      fun v => v j - ∑ i ∈ Finset.Iio j,
        (⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2) • gramSchmidt ℝ v i := by
    ext v
    rw [gramSchmidt_def]
    simp only [Submodule.starProjection_singleton]
    rfl
  rw [heq]
  apply (measurable_pi_apply j).sub
  apply Finset.measurable_sum
  intro i hi
  have hi' := ih i (Finset.mem_Iio.mp hi)
  exact ((hi'.inner (measurable_pi_apply j)).div (hi'.norm.pow_const 2)).smul hi'
end GramDistances

variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
lemma lintegral_pi_snoc (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f v ∂Measure.pi (fun _ => ν) =
      ∫⁻ v : Fin n → E, ∫⁻ x, f (Fin.snoc v x) ∂ν ∂Measure.pi (fun _ => ν) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (Fin.last n)).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f,
    lintegral_prod_symm]
  · congr 1
    ext v
    congr 1
    ext x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    exact Fin.insertNth_last' x v
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.ReplicaMoments ----
namespace OAI

/-!
Inverse Gram moments and almost-everywhere replica independence.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ReplicaMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_replicaWeight (m : ℕ) (p : E) (n : ℕ) :
    Measurable (replicaWeight m p (n := n)) := by
  have hs : Measurable (fun v : Fin n → E => fun j => v j - p) := by fun_prop
  exact Finset.measurable_prod _ fun i _ =>
    (((measurable_gramSchmidt i).comp hs).norm.inv.pow_const m).ennreal_ofReal

omit [MeasurableSpace E] [BorelSpace E] in
lemma replicaWeight_snoc (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) (x : E) :
    replicaWeight m p (Fin.snoc v x) = replicaWeight m p v *
      ENNReal.ofReal ((Metric.infDist x (AffineSubspace.mk' p
        (Submodule.span ℝ (Set.range (fun i => v i - p))) : Set E))⁻¹ ^ m) := by
  unfold replicaWeight
  rw [Fin.prod_univ_castSucc]
  simp only [gramSchmidt_castSucc, Fin.snoc_castSucc]
  rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

lemma affine_inverse_moment_le_replicaConstant {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (L : AffineSubspace ℝ E) [Nonempty L] (m : ℕ)
    (hmargin : (Module.finrank ℝ L.direction : ℝ) + (m + 1 : ℕ) ≤ a) :
    ∫⁻ x, ENNReal.ofReal ((Metric.infDist x L)⁻¹ ^ m) ∂ν ≤ replicaConstant ν a m := by
  apply (hν.affine_inverse_moment hsupport L m hmargin).trans
  dsimp [replicaConstant]
  gcongr
  · norm_num
  · exact Submodule.finrank_le L.direction

theorem replica_integral_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (m : ℕ) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν) ≤
      (replicaConstant ν a m) ^ n := by
  induction n with
  | zero => simp [replicaWeight]
  | succ n ih =>
    have hmargin' : (n : ℝ) + m ≤ a := by exact le_trans (by push_cast; linarith) hmargin
    have hinner (v : Fin n → E) :
        ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν ≤
          replicaWeight m p v * replicaConstant ν a m := by
      simp_rw [replicaWeight_snoc]
      rw [lintegral_const_mul _ (by fun_prop)]
      gcongr
      apply affine_inverse_moment_le_replicaConstant hν hsupport
      have hdim := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin] at hdim
      have hdim' : (Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => v i - p))) : ℝ) ≤ n :=
        by exact_mod_cast hdim
      rw [AffineSubspace.direction_mk']
      push_cast at hmargin ⊢
      linarith
    calc
      _ = ∫⁻ v : Fin n → E, ∫⁻ x, replicaWeight m p (Fin.snoc v x) ∂ν
          ∂Measure.pi (fun _ => ν) := lintegral_pi_snoc ν _ (measurable_replicaWeight m p (n+1))
      _ ≤ ∫⁻ v : Fin n → E, replicaWeight m p v * replicaConstant ν a m
          ∂Measure.pi (fun _ => ν) := lintegral_mono hinner
      _ = (∫⁻ v : Fin n → E, replicaWeight m p v ∂Measure.pi (fun _ => ν)) *
          replicaConstant ν a m := lintegral_mul_const _ (measurable_replicaWeight m p n)
      _ ≤ (replicaConstant ν a m)^n * replicaConstant ν a m :=
          mul_le_mul' (ih hmargin') le_rfl
      _ = _ := (pow_succ _ _).symm
end ReplicaMoments
section AePiLast
variable {E : Type*} [MeasurableSpace E] {n : ℕ} (ν : Measure E) [SigmaFinite ν]
end AePiLast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurableSet_gramSchmidt_ne_zero (p : E) (n : ℕ) :
    MeasurableSet {v : Fin n → E | ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0} := by
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  have h := (measurable_gramSchmidt i).comp
    (show Measurable (fun v : Fin n → E => fun j => v j - p) by fun_prop)
  exact (measurableSet_eq_fun h measurable_const).compl

theorem ae_gramSchmidt_ne_zero {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      ∀ i, gramSchmidt ℝ (fun j => v j - p) i ≠ 0 := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ n ih =>
    rw [ae_pi_snoc ν (measurableSet_gramSchmidt_ne_zero p (n+1))]
    have hn : (n : ℝ) ≤ a := by push_cast at hmargin; linarith
    filter_upwards [ih hn] with v hv
    let L := AffineSubspace.mk' p (Submodule.span ℝ (Set.range (fun i : Fin n => v i - p)))
    have hdim : (Module.finrank ℝ L.direction : ℝ) ≤ n := by
      dsimp [L]
      rw [AffineSubspace.direction_mk']
      have hh := finrank_range_le_card (R := ℝ) (fun i : Fin n => v i - p)
      simp only [Fintype.card_fin, Set.finrank] at hh
      exact_mod_cast hh
    have hnull : ν L = 0 := hν.affine_null hsupport L (by push_cast at hmargin; linarith)
    have ha : ∀ᵐ x ∂ν, x ∉ L := by
      rw [ae_iff]
      convert hnull using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    intro i
    induction i using Fin.lastCases with
    | last =>
      apply norm_ne_zero_iff.mp
      rw [norm_gramSchmidt_sub_eq_affine_infDist, image_Iio_last]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ne_of_gt ((L.closed_of_finiteDimensional.notMem_iff_infDist_pos
        ⟨p, AffineSubspace.self_mem_mk' _ _⟩).mp hx)
    | cast j => simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hv j

theorem ae_replica_linearIndependent {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (p : E)
    (n : ℕ) (hmargin : (n : ℝ) ≤ a) :
    ∀ᵐ v : Fin n → E ∂Measure.pi (fun _ => ν),
      LinearIndependent ℝ (fun j => v j - p) := by
  filter_upwards [ae_gramSchmidt_ne_zero hν hsupport p n hmargin] with v hv
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [det_gram_eq_prod_gramSchmidt]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hv i))

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma sqrt_det_gram (n : ℕ) (v : Fin n → E) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [det_gram_eq_prod_gramSchmidt, Real.sqrt_prod _ (fun _ _ => sq_nonneg _)]
  simp only [Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma replicaWeight_eq_det (m : ℕ) (p : E) {n : ℕ} (v : Fin n → E) :
    replicaWeight m p v = ENNReal.ofReal
      ((Real.sqrt (Matrix.gram ℝ (fun j => v j - p)).det)⁻¹ ^ m) := by
  rw [sqrt_det_gram, ← Finset.prod_inv_distrib, ← Finset.prod_pow]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)).symm

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.GaussianKernel ----
namespace OAI

/-!
Gaussian coordinate domination and replica kernel bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma lintegral_fin_prod (n : ℕ) (f : Fin n → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → X, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) =
      ∏ i, ∫⁻ x, f i x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lintegral_pi_snoc μ _ (by fun_prop)]
    simp_rw [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [lintegral_const_mul _ (hf (Fin.last n))]
    rw [lintegral_mul_const _ (by fun_prop), ih _ (fun i => hf i.castSucc)]

lemma lintegral_pow_pi (f : X → ℝ≥0∞) (hf : Measurable f) (n : ℕ) :
    (∫⁻ x, f x ∂μ)^n =
      ∫⁻ x : Fin n → X, ∏ i, f (x i) ∂Measure.pi (fun _ => μ) := by
  rw [lintegral_fin_prod μ n _ (fun _ => hf)]
  simp

end ReplicaKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Graph ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ballAverage_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R η : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R + η < ‖y - rowMap A z‖) :
    ballAverage ν m η (A,y) = 0 := by
  have hz : (ν.map (rowMap A)) (Metric.closedBall y η) = 0 := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ν.support_mem_ae] with t ht hty
    have htR : ‖t-z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hsupport ht
    have hty' : ‖y - rowMap A t‖ ≤ η := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hty
    have hn : ‖rowMap A t - rowMap A z‖ ≤ ‖rowMap A‖ * R := by
      rw [← map_sub]
      exact ((rowMap A).le_opNorm _).trans (mul_le_mul_of_nonneg_left htR (norm_nonneg _))
    have hb : ‖y - rowMap A z‖ ≤ η + ‖rowMap A‖ * R := by
      calc
        _ = ‖(y - rowMap A t) + (rowMap A t - rowMap A z)‖ := by congr 1; abel
        _ ≤ ‖y - rowMap A t‖ + ‖rowMap A t - rowMap A z‖ := norm_add_le _ _
        _ ≤ _ := add_le_add hty' hn
    linarith
  simp only [ballAverage_eq, hz, ENNReal.zero_div]

theorem lowerDensity_eq_zero_of_far (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (z : E) (R : ℝ) (y : Label m)
    (hsupport : ν.support ⊆ Metric.closedBall z R)
    (hfar : ‖rowMap A‖ * R < ‖y - rowMap A z‖) :
    lowerDensity ν m (A,y) = 0 := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : ∀ᶠ n : ℕ in atTop, ballAverage ν m ((n : ℝ) + 1)⁻¹ (A,y) = 0 := by
    filter_upwards [ht (Iio_mem_nhds (sub_pos.mpr hfar))] with n hn
    apply ballAverage_eq_zero_of_far ν m A z R _ y hsupport
    have hnn : ((n : ℝ) + 1)⁻¹ < ‖y - rowMap A z‖ - ‖rowMap A‖ * R := hn
    linarith
  exact (liminf_congr he).trans (liminf_const _)
end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma dilate_rescale (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    dilate z R (rescale z R x) = x := by
  simp [dilate, rescale, smul_smul, hR]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rescale_preimage_closedBall (z b : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    rescale z R ⁻¹' Metric.closedBall b t = Metric.closedBall (dilate z R b) (R*t) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have he : rescale z R x - b = R⁻¹ • (x - dilate z R b) := by
    simp [rescale, dilate, smul_sub, smul_add, smul_smul, hR.ne', sub_sub, add_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [inv_mul_le_iff₀ hR]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma normalizedRescale_finite (ν : Measure E) [IsFiniteMeasure ν]
    (K a : ℝ) (z : E) (R : ℝ) (hKR : 0 < K * R ^ a) :
    IsFiniteMeasure (normalizedRescale ν K a z R) := by
  dsimp [normalizedRescale]
  exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hKR))

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_local {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R) :
    NoiselessRegression.HasLocalMassBound (normalizedRescale ν K a z R) a := by
  intro b _ t ht
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall z b hR]
  apply (mul_le_mul' le_rfl (hν (dilate z R b) (R*t) (mul_pos hR ht))).trans
  rw [Real.mul_rpow hR.le ht.le, ← mul_assoc,
    ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hR.le a)),
    ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
      ENNReal.ofReal_ne_top, one_mul]

omit [FiniteDimensional ℝ E] in
lemma normalizedRescale_recover (ν : Measure E) (K a : ℝ) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (K * R ^ a) • (normalizedRescale ν K a z R).map (dilate z R) = ν := by
  rw [normalizedRescale, Measure.map_smul _ _ (dilate z R), smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top,
    one_smul, Measure.map_map (measurable_dilate z R) (measurable_rescale z R)]
  have he : dilate z R ∘ rescale z R = id := by
    funext x; exact dilate_rescale z hR.ne' x
  rw [he, Measure.map_id]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma ballAverage_smul (ν : Measure E) (c : ℝ≥0∞) (m : ℕ) (η : ℝ)
    (A : Fin m → E) (y : Label m) :
    ballAverage (c • ν) m η (A,y) = c * ballAverage ν m η (A,y) := by
  simp only [ballAverage, vectorSmoothing, lintegral_smul_measure, smul_eq_mul]

lemma ballAverage_dilate (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η) (A : Fin m → E) (b : Label m) :
    ballAverage (ν.map (dilate z R)) m η (A, rowMap A z + b) =
      (ENNReal.ofReal (R ^ m))⁻¹ * ballAverage ν m (η/R) (A, R⁻¹ • b) := by
  rw [ballAverage_eq, ballAverage_eq]
  have hn : ((ν.map (dilate z R)).map (rowMap A)) (Metric.closedBall (rowMap A z + b) η) =
      (ν.map (rowMap A)) (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet,
      Measure.map_apply (measurable_dilate z R)
        (Metric.isClosed_closedBall.measurableSet.preimage (rowMap A).continuous.measurable),
      Measure.map_apply (rowMap A).continuous.measurable Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    have he : rowMap A (dilate z R x) - (rowMap A z + b) =
        R • (rowMap A x - R⁻¹ • b) := by
      simp only [dilate, map_add, map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hR, le_div_iff₀ hR, mul_comm]
  have hv : volume (Metric.closedBall (rowMap A z + b) η) =
      ENNReal.ofReal (R ^ m) * volume (Metric.closedBall (R⁻¹ • b) (η/R)) := by
    rw [Measure.addHaar_closedBall volume _ hη.le,
      Measure.addHaar_closedBall volume _ (div_pos hη hR).le,
      finrank_euclideanSpace_fin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← mul_pow, mul_div_cancel₀ _ hR.ne']
  rw [hn, hv, ENNReal.div_eq_inv_mul, ENNReal.mul_inv
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))) (Or.inl ENNReal.ofReal_ne_top)]
  rw [ENNReal.div_eq_inv_mul, mul_assoc]

lemma normalizedRescale_mass {ν : Measure E} {K a : ℝ} (hν : AllBallMass ν K a)
    (hK : 0 < K) (z : E) {R : ℝ} (hR : 0 < R)
    (hsupport : ν.support ⊆ Metric.closedBall z R) :
    normalizedRescale ν K a z R Set.univ ≤ 1 := by
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    apply propext
    exact iff_of_true (Set.mem_univ x) (hsupport hx)
  rw [normalizedRescale, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_rescale z R) MeasurableSet.univ, Set.preimage_univ, he]
  exact (mul_le_mul' le_rfl (hν z R hR)).trans_eq
    (ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top)

lemma ballAverage_normalizedRescale {ν : Measure E} [IsFiniteMeasure ν]
    (K a : ℝ) (hK : 0 < K) (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (m : ℕ) (A : Fin m → E) (b : Label m) :
    ballAverage ν m η (A, rowMap A z + b) =
      ENNReal.ofReal (K * R ^ (a-m)) *
        ballAverage (normalizedRescale ν K a z R) m (η/R) (A, R⁻¹ • b) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  conv_lhs => rw [← normalizedRescale_recover ν K a hK z hR]
  rw [ballAverage_smul, ballAverage_dilate μ m z hR hη, ← mul_assoc]
  congr 1
  rw [Real.rpow_sub_natCast hR.ne', ← mul_div_assoc, ENNReal.ofReal_div_of_pos (by positivity)]
  rfl

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_vector_replica_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (m : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      φ (fun j => y j - ⟪p, A j⟫) *
        ∏ i, φ (fun j => y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i-p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, φ (fun j => y j - ⟪p, A j⟫) *
        ∏ i, φ (fun j => y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, φ y * ∏ i, φ (fun j => y j - ⟪v i-p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) :
        (fun j => y j - ⟪p, A j⟫ - ⟪v i-p, A j⟫) =
        (fun j => y j - ⟪v i, A j⟫) := by
      funext j; rw [inner_sub_left]; ring
    convert (lintegral_sub_right_eq_self (μ := (volume : Measure (Fin m → ℝ)))
        (fun y : Fin m → ℝ => φ y * ∏ i, φ (fun j => y j - ⟪v i-p, A j⟫))
        (fun j => ⟪p, A j⟫)) using 1
    apply lintegral_congr
    intro y
    simp only [Pi.sub_apply, he]
    rfl
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y, φ y * ENNReal.ofReal
        ((∏ i, ‖gramSchmidt ℝ (fun i => v i-p) i‖)⁻¹ ^ m) := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [lintegral_const_mul _ (by fun_prop)]
      exact mul_le_mul' le_rfl (gaussian_graph_kernel_bound _ hv m φ hφ hφ1 y)
    _ = _ := by rw [lintegral_mul_const _ hφ, hφ1, one_mul]

lemma vectorSmoothing_pow (ν : Measure E) [IsFiniteMeasure ν]
    (m n : ℕ) (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (vectorSmoothing ν m φ z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        φ (fun j => z.2 j - ⟪w.1, z.1 j⟫) *
          ∏ i, φ (fun j => z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, φ (fun j => z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← NoiselessRegression.lintegral_pow_pi ν
    (fun t : E => φ (fun j => z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem vectorSmoothing_integrated_moment {m : ℕ} {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ y, φ y = 1)
    (n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ), (vectorSmoothing ν m φ z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  simp_rw [vectorSmoothing_pow ν m n φ hφ]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, NoiselessRegression.replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [NoiselessRegression.ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), NoiselessRegression.replicaWeight_eq_det,
        NoiselessRegression.sqrt_det_gram]
      exact gaussian_vector_replica_bound p v hv m φ hφ hφ1
    _ ≤ ∫⁻ _p, (NoiselessRegression.replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => NoiselessRegression.replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]

theorem ballAverage_integrated_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) {η : ℝ} (hη : 0 < η) :
    ∫⁻ z : (Fin m → E) × Label m, (ballAverage ν m η z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have hm := (MeasurePreserving.id (Measure.pi (fun _ : Fin m => stdGaussian E))).prod
    (PiLp.volume_preserving_toLp (Fin m))
  rw [← hm.lintegral_comp ((measurable_ballAverage ν m η).pow_const (n+1))]
  exact vectorSmoothing_integrated_moment hν hsupport _ (measurable_ballKernel m η)
    (ballKernel_integral m hη) n hmargin

end ProjectionMoments
end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.GaussianDensity ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
      (hf.comp e.symm.measurable).indicator hs) e.measurable]
  have he (x : X) : s.indicator (fun y => f (e.symm y)) (e x) =
      (e ⁻¹' s).indicator f x := by
    by_cases hx : e x ∈ s <;> simp [hx]
  simp_rw [he]
  exact (lintegral_indicator (hs.preimage e.measurable) f).symm

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Frames ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {E}

variable [MeasurableSpace E] [BorelSpace E]

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_rowMap_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {u : Fin m → E} (hu : Orthonormal ℝ u) :
    ‖rowMap u‖ ≤ 1 := by
  apply (rowMap u).opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  have h := hu.sum_inner_products_le (x := x) (s := Finset.univ)
  apply (sq_le_sq₀ (norm_nonneg (rowMap u x)) (norm_nonneg x)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [rowMap_apply, Real.norm_eq_abs, sq_abs,
    WithLp.ofLp_toLp, real_inner_comm] using h

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_eq_toLp_coordinateMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    (rowMap A : E → Label m) = (WithLp.toLp 2) ∘ coordinateMap A := rfl

lemma coordinateDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    volume.withDensity (fun y => coordinateDensity ν m (A,y)) = ν.map (coordinateMap A) := by
  have hr : ν.map (rowMap A) ≪ (volume : Measure (Label m)) := by
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin m)).map_eq]
    exact hA.map (by fun_prop)
  have h := congrArg (fun μ : Measure (Label m) => μ.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm)
    (lowerDensity_is_density ν m A hr)
  rw [map_withDensity_equiv _ _ _ (by fun_prop),
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma orbitMoment_eq_frame (ν : Measure E) [SFinite ν] (m n : ℕ) (u : Fin m → E) :
    orbitMoment ν m n u = ∫⁻ A, labelMoment ν m n A ∂frameLaw u := by
  rw [frameLaw, lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_left u)]
  rfl

end ProjectionMoments
end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.FrameMoments ----
namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_ballAverage
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma replicaConstant_real_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : Measure E} (hν : ν Set.univ ≤ 1) {a : ℝ} {m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    NoiselessRegression.replicaConstant ν a m ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E := by
  apply le_trans _ (NoiselessRegression.replicaConstant_le hν hd le_rfl hm)
  have hr : (4 : ℝ)^a ≤ (4 : ℝ)^(Module.finrank ℝ E : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hc : ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^a) ≤
      ENNReal.ofReal ((3 : ℝ)^Module.finrank ℝ E * 4^(Module.finrank ℝ E : ℝ)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hr (by positivity))
  exact add_le_add le_rfl (mul_le_mul' hc le_rfl)

lemma lintegral_inv_smul_label {m : ℕ} (f : Label m → ℝ≥0∞)
    (hf : Measurable f) {R : ℝ} (hR : 0 < R) :
    ∫⁻ y, f (R⁻¹ • y) = ENNReal.ofReal (R^m) * ∫⁻ y, f y := by
  rw [← lintegral_map hf (by fun_prop), Measure.map_addHaar_smul volume (inv_ne_zero hR.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hR.le m),
    lintegral_smul_measure, smul_eq_mul]

lemma ballAverage_label_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hK : 0 < K) (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (m n : ℕ) (A : Fin m → E) :
    (∫⁻ y : Label m, ballAverage ν m η (A,y)^(n+1)) =
      (ENNReal.ofReal (K*R^(a-m)))^(n+1) * ENNReal.ofReal (R^m) *
        ∫⁻ y : Label m, ballAverage (normalizedRescale ν K a z R) m (η/R) (A,y)^(n+1) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  rw [← lintegral_add_left_eq_self (fun y : Label m => ballAverage ν m η (A,y)^(n+1)) (rowMap A z)]
  simp_rw [ballAverage_normalizedRescale K a hK z hR hη, mul_pow]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_inv_smul_label (fun y : Label m => ballAverage (normalizedRescale ν K a z R) m (η/R) (A,y)^(n+1)) (by fun_prop) hR,
    mul_assoc]

theorem ballAverage_integrated_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R η : ℝ} (hR : 0 < R) (hη : 0 < η)
    (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    ∫⁻ x : (Fin m → E) × Label m, ballAverage ν m η x^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  let μ := normalizedRescale ν K a z R
  have : IsFiniteMeasure μ := normalizedRescale_finite ν K a z R (by positivity)
  rw [lintegral_prod _ (by fun_prop)]
  simp_rw [ballAverage_label_scaled (ν := ν) (a := a) hK z hR hη m n]
  rw [lintegral_const_mul _ (by fun_prop)]
  apply mul_le_mul' le_rfl
  rw [← lintegral_prod _ (show AEMeasurable (fun x : (Fin m → E) × Label m =>
    ballAverage μ m (η/R) x^(n+1)) _ by fun_prop)]
  apply (ballAverage_integrated_moment (normalizedRescale_local hν hK z hR)
    (normalizedRescale_support K a z hR hs) m n hmargin (div_pos hη hR)).trans
  have hmass := normalizedRescale_mass hν hK z hR hs
  simpa only [one_mul, pow_mul] using mul_le_mul' hmass
    (pow_le_pow_left' (replicaConstant_real_le hmass hd ha hm) n)

theorem lowerDensity_integrated_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    ∫⁻ x : (Fin m → E) × Label m, lowerDensity ν m x^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
      ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  have hp (v : ℕ → ℝ≥0∞) : (liminf v atTop)^(n+1) =
      liminf (fun j => v j^(n+1)) atTop :=
    (show Monotone (fun x : ℝ≥0∞ => x^(n+1)) from
      (fun _ _ h => pow_le_pow_left' h (n+1))).map_liminf_of_continuousAt
      v (ENNReal.continuous_pow (n+1)).continuousAt
  simp only [lowerDensity, hp]
  apply (lintegral_liminf_le (fun j => (measurable_ballAverage ν m _).pow_const _)).trans
  apply liminf_le_of_frequently_le'
  exact Filter.Frequently.of_forall (fun j => ballAverage_integrated_scaled hν hK z hR
    (inv_pos.mpr (by positivity)) hs m n hmargin hd ha hm)

theorem gaussian_labelMoment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) :
    ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(Module.finrank ℝ E*n) := by
  have he (A : Fin m → E) : labelMoment ν m n A =
      ∫⁻ y : Label m, lowerDensity ν m (A,y)^(n+1) :=
    (PiLp.volume_preserving_toLp (Fin m)).lintegral_comp
      (show Measurable (fun y : Label m => lowerDensity ν m (A,y)^(n+1)) by fun_prop)
  simp_rw [he]
  rw [← lintegral_prod _ (show AEMeasurable (fun x : (Fin m → E) × Label m =>
    lowerDensity ν m x^(n+1)) _ by fun_prop)]
  exact lowerDensity_integrated_scaled hν hK z hR hs m n hmargin hd ha hm

theorem frame_moment_scaled {ν : Measure E} [IsFiniteMeasure ν]
    {K a : ℝ} (hν : AllBallMass ν K a) (hK : 0 < K)
    (z : E) {R : ℝ} (hR : 0 < R) (hs : ν.support ⊆ Metric.closedBall z R)
    (m n : ℕ) (hmargin : (n : ℝ)+m ≤ a)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    ∫⁻ A, labelMoment ν m n A ∂frameLaw u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2*Module.finrank ℝ E))^(m*n) *
        (ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
          (128 : ℝ≥0∞)^(Module.finrank ℝ E*n)) := by
  rw [← orbitMoment_eq_frame]
  exact (frame_gaussian_comparison ν hm hd u hu hac).trans
    (mul_le_mul' le_rfl (gaussian_labelMoment_scaled hν hK z hR hs m n hmargin hd ha hm))

end

lemma ennreal_root_bound {q : ℕ} (hq : q ≠ 0) {v : ℝ≥0∞} {B : ℝ}
    (hB : 0 ≤ B) (h : v ≤ ENNReal.ofReal B ^ q) :
    v ^ (1/(q:ℝ)) ≤ ENNReal.ofReal B := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hh := ENNReal.rpow_le_rpow h (by positivity : 0 ≤ 1/(q:ℝ))
  rwa [← ENNReal.ofReal_pow hB,
    ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hB q) (by positivity),
    ← Real.rpow_natCast_mul hB, mul_one_div_cancel hq', Real.rpow_one] at hh

lemma frame_cost_root {d m n : ℕ} (hd : 1 ≤ d) (hm : m ≤ d)
    (a K R : ℝ) (hK : 0 ≤ K) (hR : 0 < R) {v : ℝ≥0∞}
    (h : v ≤ (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2*d))^(m*n) *
      (ENNReal.ofReal (K*R^(a-m))^(n+1) * ENNReal.ofReal (R^m) *
        (128 : ℝ≥0∞)^(d*n))) :
    v ^ (1/((n:ℝ)+1)) ≤
      ENNReal.ofReal ((256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
        R^(a-(m:ℝ)*(1-1/((n:ℝ)+1)))) := by
  have hb := ENNReal.ofReal_le_ofReal (frame_cost_power (n := n) hd hm a K R hK hR)
  simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    ENNReal.ofReal_ofNat] at hb
  simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow] at h
  have hB : 0 ≤ (256 : ℝ)^d * (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1))) := by positivity
  have hb' : v ≤ (ENNReal.ofReal ((256 : ℝ)^d *
      (256*Real.sqrt d)^((m:ℝ)*(1-1/((n:ℝ)+1))) * K *
      R^(a-(m:ℝ)*(1-1/((n:ℝ)+1)))))^(n+1) := by
    simp (discharger := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_ofNat]
    exact h.trans hb
  have hh := ennreal_root_bound (show n+1 ≠ 0 by omega) hB hb'
  simpa only [Nat.cast_add, Nat.cast_one] using hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
lemma measure_eq_zero_of_allBall_zero [BorelSpace E] {ν : Measure E} {a : ℝ}
    (hν : AllBallMass ν 0 a) (z : E) {R : ℝ} (hR : 0 < R)
    (hs : ν.support ⊆ Metric.closedBall z R) : ν = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  have he : ν Set.univ = ν (Metric.closedBall z R) := by
    apply measure_congr
    filter_upwards [ν.support_mem_ae] with x hx
    exact propext (iff_of_true (Set.mem_univ x) (hs hx))
  rw [he]
  apply le_antisymm _ bot_le
  simpa using hν z R hR

lemma coordinateDensity_frame_support (ν : Measure E) [IsFiniteMeasure ν] {m : ℕ}
    (z : E) {R : ℝ} (hR : 0 ≤ R) (hs : ν.support ⊆ Metric.closedBall z R)
    (A : Fin m → E) (hA : Orthonormal ℝ A) (y : Fin m → ℝ)
    (hy : R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖) :
    coordinateDensity ν m (A,y) = 0 := by
  apply lowerDensity_eq_zero_of_far ν m A z R (WithLp.toLp 2 y) hs
  have he : WithLp.toLp 2 (y-coordinateMap A z) = WithLp.toLp 2 y - rowMap A z := rfl
  rw [he] at hy
  exact (show ‖rowMap A‖ * R ≤ R from by nlinarith [norm_rowMap_le hA]).trans_lt hy

theorem integrated_frame_moment :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d k q : ℕ) (β K R : ℝ)
      (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
      (z : EuclideanSpace ℝ (Fin d)) (u : Fin k → EuclideanSpace ℝ (Fin d)),
      1 ≤ k → 2 ≤ q → k+q ≤ d → 0 < β → β ≤ d →
      1 ≤ β-k-((q:ℝ)-2) → 0 ≤ K → 0 < R →
      ν.support ⊆ Metric.closedBall z R → AllBallMass ν K β →
      Orthonormal ℝ u →
      (∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) →
      Measurable (coordinateDensity ν k) ∧
      (∀ᵐ A ∂frameLaw u,
        (volume : Measure (Fin k → ℝ)).withDensity (fun y => coordinateDensity ν k (A,y)) =
          ν.map (coordinateMap A)) ∧
      (∀ (A : Fin k → EuclideanSpace ℝ (Fin d)), Orthonormal ℝ A →
        ∀ y : Fin k → ℝ,
          R < ‖WithLp.toLp 2 (y-coordinateMap A z)‖ → coordinateDensity ν k (A,y) = 0) ∧
      (∫⁻ A, ∫⁻ y : Fin k → ℝ, coordinateDensity ν k (A,y)^q ∂volume ∂frameLaw u) ^ (1/(q:ℝ)) ≤
        ENNReal.ofReal (C^d * (C*Real.sqrt d)^((k:ℝ)*(1-1/(q:ℝ))) *
          K * R^(β-(k:ℝ)*(1-1/(q:ℝ)))) := by
  refine ⟨256, by norm_num, ?_⟩
  intro d k q β K R ν _ z u hk hq hdim hβ hβd hmargin hK hR hs hν hu hac
  refine ⟨measurable_coordinateDensity ν k, ?_, ?_, ?_⟩
  · filter_upwards [hac] with A hA
    exact coordinateDensity_is_density ν k A hA
  · intro A hA y hy
    exact coordinateDensity_frame_support ν z hR.le hs A hA y hy
  · rcases eq_or_lt_of_le hK with hK0 | hK0
    · have hzero : ν = 0 := measure_eq_zero_of_allBall_zero (hK0 ▸ hν) z hR hs
      subst ν
      simp only [coordinateDensity_zero, zero_pow (by omega : q ≠ 0), lintegral_zero]
      rw [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1/(q:ℝ))]
      exact bot_le
    · have hn : q-1+1 = q := by omega
      have hnR : ((q-1:ℕ):ℝ)+1 = q := by exact_mod_cast hn
      have hmm : ((q-1:ℕ):ℝ)+k ≤ β := by linarith
      have h := frame_moment_scaled hν hK0 z hR hs k (q-1) hmm
        (by simpa using (show 1 ≤ d by omega)) (by simpa using hβd)
        (by simpa using (show k ≤ d by omega)) u hu hac
      have ht := frame_cost_root (d := d) (m := k) (n := q-1) (by omega) (by omega)
        β K R hK hR (by simpa only [finrank_euclideanSpace_fin] using h)
      simpa only [labelMoment, hn, hnR] using ht

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.integrated_frame_moment := @_root_.OAI.ProjectionMoments.integrated_frame_moment
