-- Prove2me | solution 1 for OAI.NoiselessRegression.continuation_mass_bound_ceil
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:21:01.864547+00:00
-- url     : https://prove2.me/submissions/69343ded-1162-4a89-8dc8-91ef4e9b1957

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Stopping.lean:L19-L78
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.continuation_mass_bound_ceil. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Theorems.Thm_OAI_NoiselessRegression_ae_pi_snoc
import Theorems.Thm_OAI_NoiselessRegression_card_le_volume_ratio
import Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound
import Theorems.Thm_OAI_NoiselessRegression_replicaConstant_le

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

lemma orthonormal_gaussian_map {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) :
    (stdGaussian E).map (fun x => fun i => ⟪u i, x⟫) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  let f : E → EuclideanSpace ℝ (Fin n) := fun x => WithLp.toLp 2 (fun i => ⟪u i, x⟫)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have he : (stdGaussian E).map f = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    apply Measure.ext_of_charFun
    ext t
    have hi (x : E) : ⟪f x, t⟫ = ⟪x, ∑ i, t i • u i⟫ := by
      simp [f, PiLp.inner_apply, inner_sum, inner_smul_right, real_inner_comm x]
    have hn : ‖∑ i, t i • u i‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hu.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [pow_two]
    rw [charFun_apply, integral_map hf.aemeasurable (by fun_prop)]
    simp_rw [hi]
    change charFun (stdGaussian E) (∑ i, t i • u i) = _
    rw [charFun_stdGaussian, charFun_stdGaussian]
    congr 2
    exact_mod_cast congrArg Neg.neg hn
  have h := congrArg (Measure.map (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))) he
  rw [← map_pi_eq_stdGaussian] at h
  simpa [Measure.map_map (WithLp.measurable_ofLp _ _) hf,
    Measure.map_map (WithLp.measurable_ofLp _ _) (WithLp.measurable_toLp _ _),
    Function.comp_def, f, WithLp.ofLp_toLp, Measure.map_id] using h

lemma gaussianReal_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  conv_rhs => rw [← withDensity_one (μ := (volume : Measure ℝ))]
  apply withDensity_mono
  filter_upwards [] with x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤ 1
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  have hs : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ≥0)) := by
    norm_num only [NNReal.coe_one, mul_one]
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  have he : Real.exp (-(x - 0)^2 / (2 * (1 : ℝ≥0))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hs)).trans he
lemma measure_pi_mono {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {μ ν : ∀ i, Measure (X i)}
    (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod (fun _ _ => zero_le) fun i _ => h i (s i))
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  exact ho s

lemma pi_gaussianReal_le_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≤ (volume : Measure (Fin n → ℝ)) :=
  measure_pi_mono (fun _ => gaussianReal_le_volume)
lemma gaussian_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i, x⟫) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹) •
        (volume : Measure (Fin n → ℝ)) := by
  let u := gramSchmidtNormed ℝ v
  let R : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ v i‖) * gsUpper n v
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hv
  have hn (i : Fin n) : ‖gramSchmidt ℝ v i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)
  have hexp (j : Fin n) : ∑ i, R i j • u i = v j := by
    rw [← gsUpper_expansion n v j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
    dsimp only [R]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal, gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  have hpos : 0 ≤ R.transpose.det := by rw [hdet]; positivity
  have hf : Measurable (Matrix.toLin' R.transpose) :=
    (Matrix.toLin' R.transpose).continuous_of_finiteDimensional.measurable
  have heq : (fun x : E => fun j => ⟪v j, x⟫) =
      (Matrix.toLin' R.transpose) ∘ (fun x => fun i => ⟪u i, x⟫) := by
    funext x j
    rw [← hexp j]
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sum_inner,
      inner_smul_left]
  rw [heq, ← Measure.map_map hf (by fun_prop), orthonormal_gaussian_map hu]
  calc
    _ ≤ (volume : Measure (Fin n → ℝ)).map (Matrix.toLin' R.transpose) :=
      Measure.map_mono (pi_gaussianReal_le_volume n) hf
    _ = _ := by
      rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
        abs_of_nonneg (inv_nonneg.mpr hpos), hdet]
lemma measure_pi_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Measure.pi (fun i => c • μ i) = c ^ Fintype.card ι • Measure.pi μ := by
  lift c to ℝ≥0 using hc
  simp_rw [Measure.coe_nnreal_smul]
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

lemma gaussian_rows_pairings_le {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j i => ⟪v i, A j⟫) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable
    (fun x : E => fun i => ⟪v i, x⟫)).aemeasurable)]
  have h := measure_pi_mono (fun _ : Fin m => gaussian_pairings_le v hv)
  rw [measure_pi_smul _ _ ENNReal.ofReal_ne_top] at h
  rw [ENNReal.ofReal_pow (by positivity)]
  simpa only [Fintype.card_fin, volume_pi] using h
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

lemma lintegral_product_differences (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ x, φ x = 1) (m n : ℕ) (y : Fin m → ℝ) :
    ∫⁻ z : Fin m → Fin n → ℝ,
      ∏ j, φ (y j) * ∏ i, φ (y j - z j i) = ∏ j, φ (y j) := by
  rw [volume_pi, lintegral_fin_prod (volume : Measure (Fin n → ℝ)) m
    (fun j z => φ (y j) * ∏ i, φ (y j - z i)) (by intro i; fun_prop)]
  apply Finset.prod_congr rfl
  intro j _
  rw [lintegral_const_mul _ (by fun_prop), volume_pi,
    lintegral_fin_prod (volume : Measure ℝ) n
      (fun _ z => φ (y j - z)) (by intro i; fun_prop)]
  simp_rw [lintegral_sub_left_eq_self φ (y j), hφ1]
  simp

end ReplicaKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_rows_kernel_bound {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m : ℕ) (y : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) * ∏ j, φ (y j) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun z => ∏ j, φ (y j) * ∏ i, φ (y j - z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have heq (A : Fin m → E) :
      (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫) =
      H (fun j i => ⟪v i, A j⟫) := by
    dsimp [H]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure]
      change _ * (∫⁻ z : Fin m → Fin n → ℝ, ∏ j, φ (y j) * ∏ i, φ (y j - z j i)) = _
      rw [lintegral_product_differences φ hφ hφ1]

lemma gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - ⟪p, A j⟫)) *
        ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) (j : Fin m) :
        y j - ⟪p, A j⟫ - ⟪v i - p, A j⟫ = y j - ⟪v i, A j⟫ := by
      rw [inner_sub_left]
      ring
    simpa only [Pi.sub_apply, he] using
      lintegral_sub_right_eq_self
        (fun y : Fin m → ℝ => (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫))
        (fun j => ⟪p, A j⟫)
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : Fin m → ℝ,
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) *
        ∏ j, φ (y j) := lintegral_mono fun y =>
          gaussian_rows_kernel_bound (fun i => v i - p) hv φ hφ hφ1 m y
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume m (fun _ => φ) (fun _ => hφ)]
      simp [hφ1]

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Smoothing ----
namespace OAI

/-!
Projection smoothing, Gaussian noise, and bounds under weak limits.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_projectionSmoothing (ν : Measure E) [SFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m : ℕ) :
    Measurable (projectionSmoothing ν φ m) := by
  apply Measurable.lintegral_prod_right
  fun_prop

lemma projectionSmoothing_pow (ν : Measure E) [SigmaFinite ν]
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (m n : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) :
    (projectionSmoothing ν φ m z)^(n+1) =
      ∫⁻ w : E × (Fin n → E),
        (∏ j, φ (z.2 j - ⟪w.1, z.1 j⟫)) *
          ∏ i, ∏ j, φ (z.2 j - ⟪w.2 i, z.1 j⟫)
        ∂ν.prod (Measure.pi (fun _ => ν)) := by
  rw [lintegral_prod _ (by fun_prop)]
  have hG : Measurable (fun v : Fin n → E =>
      ∏ i, ∏ j, φ (z.2 j - ⟪v i, z.1 j⟫)) := by fun_prop
  simp_rw [lintegral_const_mul _ hG]
  rw [lintegral_mul_const _ (by fun_prop), ← lintegral_pow_pi ν
    (fun t : E => ∏ j, φ (z.2 j - ⟪t, z.1 j⟫)) (by fun_prop) n]
  exact pow_succ' _ _

theorem projectionSmoothing_moment {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ z : (Fin m → E) × (Fin m → ℝ),
      (projectionSmoothing ν φ m z)^(n+1)
      ∂(Measure.pi (fun _ => stdGaussian E)).prod volume ≤
       ν Set.univ * (replicaConstant ν a m)^n := by
  simp_rw [projectionSmoothing_pow ν φ hφ m n]
  rw [lintegral_lintegral_swap (by fun_prop), lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ p, ∫⁻ v : Fin n → E, replicaWeight m p v
        ∂Measure.pi (fun _ => ν) ∂ν := by
      apply lintegral_mono
      intro p
      apply lintegral_mono_ae
      filter_upwards [ae_replica_linearIndependent hν hsupport p n
        (le_trans (le_add_of_nonneg_right (Nat.cast_nonneg m)) hmargin)] with v hv
      rw [lintegral_prod _ (by fun_prop), replicaWeight_eq_det, sqrt_det_gram]
      exact gaussian_replica_kernel_bound p v hv φ hφ hφ1 m
    _ ≤ ∫⁻ _p, (replicaConstant ν a m)^n ∂ν :=
      lintegral_mono fun p => replica_integral_bound hν hsupport m p n hmargin
    _ = _ := by rw [lintegral_const, mul_comm]
end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

lemma measure_pi_withDensity (n : ℕ) (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite (μ.withDensity (f i))] :
    Measure.pi (fun i => μ.withDensity (f i)) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have he (x : Fin n → X) :
      (Set.univ.pi s).indicator (fun x => ∏ i, f i (x i)) x =
        ∏ i, (s i).indicator (f i) (x i) := by
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      have : ∃ i, x i ∉ s i := by simpa only [Set.mem_univ_pi, not_forall] using hx
      obtain ⟨i, hi⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  simp_rw [he]
  rw [lintegral_fin_prod μ n _ (fun i => (hf i).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
end ProductDensity

lemma pi_gaussian_map_scale (m : ℕ) (δ : ℝ) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
      (fun u => fun j => δ * u j) =
      Measure.pi (fun _ : Fin m => gaussianReal 0 (NNReal.mk (δ^2) (sq_nonneg δ))) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : ℝ => δ * x)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => δ * x)).aemeasurable)]
  simp_rw [gaussianReal_map_const_mul, mul_zero, mul_one]

lemma pi_gaussian_withDensity (m : ℕ) (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 v) =
      (volume : Measure (Fin m → ℝ)).withDensity (fun y => ∏ j, gaussianPDF 0 v (y j)) := by
  simp_rw [gaussianReal_of_var_ne_zero _ hv]
  have : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  rw [measure_pi_withDensity (volume : Measure ℝ) m
    (fun _ => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v)]
  rfl
lemma lintegral_gaussian_shift_scale (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0)
    (a : Fin m → ℝ) (f : (Fin m → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
      ∂Measure.pi (fun _ => gaussianReal 0 1) =
    ∫⁻ y : Fin m → ℝ, (∏ j, gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ)) (y j - a j)) * f y := by
  let v : ℝ≥0 := NNReal.mk (δ^2) (sq_nonneg δ)
  have hv : v ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  have he :
      (∫⁻ u : Fin m → ℝ, f (fun j => a j + δ * u j)
        ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫⁻ y : Fin m → ℝ, f (a + y) ∂Measure.pi (fun _ => gaussianReal 0 v) := by
    rw [← pi_gaussian_map_scale m δ, lintegral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, pi_gaussian_withDensity m v hv,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have hh (y : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 v (y j)) * f (a + y) =
      (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) (a + y) := by
    simp only [Pi.add_apply, add_sub_cancel_left]
  exact (lintegral_congr (μ := volume) hh).trans (lintegral_add_left_eq_self
    (μ := volume) (fun z : Fin m → ℝ => (∏ j, gaussianPDF 0 v (z j - a j)) * f z) a)

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma withDensity_apply_le_moment (f : X → ℝ≥0∞) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∫⁻ x, f x ^ p ∂μ ≤ C) (S : Set X) (hS : MeasurableSet S) :
    μ.withDensity f S ≤ C^(1/p) * (μ S)^(1 - 1/p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) hpq
    hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have he : 1 / (Real.conjExponent p) = 1 - 1/p := by
    have hh := hpq.inv_add_inv_eq_one
    simpa only [one_div] using (eq_sub_of_add_eq' hh)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, he] at h
  rw [withDensity_apply _ hS]
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow
    ((lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans hC) (by positivity)) le_rfl)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

lemma map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by
  let f : ℕ → X → ℝ≥0∞ := fun k => (Fₖ k ⁻¹' U).indicator (fun _ => 1)
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_const.indicator (hU.measurableSet.preimage (hFₖ k))
  have hind : ∀ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      atTop.liminf (fun k => f k x) := by
    intro x
    by_cases hx : F x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' U from hx)]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(ht x).eventually (hU.mem_nhds hx)] with k hk
      change 1 ≤ (Fₖ k ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [Set.indicator_of_mem (show x ∈ Fₖ k ⁻¹' U from hk)]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' U from hx)]
      exact zero_le
  calc
    (ρ.map F) U = ∫⁻ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ρ := by
      rw [Measure.map_apply hF hU.measurableSet,
        lintegral_indicator (hU.measurableSet.preimage hF)]
      simp
    _ ≤ ∫⁻ x, atTop.liminf (fun k => f k x) ∂ρ := lintegral_mono hind
    _ ≤ atTop.liminf (fun k => ∫⁻ x, f k x ∂ρ) := lintegral_liminf_le hf
    _ ≤ _ := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      apply Filter.Eventually.frequently
      filter_upwards [] with k
      have hk := hbound k U hU
      simpa [f, lintegral_indicator (hU.measurableSet.preimage (hFₖ k)),
        Measure.map_apply (hFₖ k) hU.measurableSet] using hk
end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

lemma ennreal_rpow_iInf {ι : Sort*} (f : ι → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    (⨅ i, f i)^α = ⨅ i, (f i)^α :=
  (ENNReal.orderIsoRpow α hα).map_iInf f

lemma measure_apply_le_of_isOpen (μ τ : Measure Y) [τ.OuterRegular]
    {C : ℝ≥0∞} (hC : C ≠ ∞) {α : ℝ} (hα : 0 < α)
    (hbound : ∀ U, IsOpen U → μ U ≤ C * (τ U)^α) (S : Set Y) :
    μ S ≤ C * (τ S)^α := by
  by_cases hC0 : C = 0
  · simp only [hC0, zero_mul] at hbound ⊢
    exact (measure_mono (Set.subset_univ S)).trans (hbound Set.univ isOpen_univ)
  rw [S.measure_eq_iInf_isOpen τ]
  simp_rw [ennreal_rpow_iInf _ hα, ENNReal.mul_iInf_of_ne hC0 hC]
  exact le_iInf fun U => le_iInf fun hSU => le_iInf fun hU =>
    (measure_mono hSU).trans (hbound U hU)

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Projection ----
namespace OAI

/-!
Exact noiseless projection laws and completed-event bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_noisyObservation (m : ℕ) (δ : ℝ) :
    Measurable (noisyObservation (E := E) m δ) := by
  unfold noisyObservation
  fun_prop

lemma gaussianCoupling_map_noisyObservation_zero (ν : Measure E) [SigmaFinite ν] (m : ℕ) :
    (gaussianCoupling ν m).map (noisyObservation m 0) = projectionLaw ν m := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m 0),
    projectionLaw, lintegral_map hf (by fun_prop)]
  dsimp [gaussianCoupling, noisyObservation]
  simp only [zero_mul, add_zero]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma gaussianCoupling_map_noisyObservation (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (gaussianCoupling ν m).map (noisyObservation m δ) =
      (matrixLabelReference (E := E) m).withDensity
        (projectionSmoothing ν (gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ))) m) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_noisyObservation m δ),
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hf]
  dsimp [gaussianCoupling, matrixLabelReference, noisyObservation]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by
    exact ((measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _).mul hf).aemeasurable)]
  apply lintegral_congr
  intro A
  rw [lintegral_prod _ (by fun_prop)]
  have he (p : E) := lintegral_gaussian_shift_scale m δ hδ
    (fun j => ⟪p, A j⟫) (fun y => f (A, y)) (hf.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [lintegral_mul_const _ (by fun_prop)]
  rfl
lemma matrixLabelReference_outerRegular (m : ℕ) :
    (matrixLabelReference (E := E) m).OuterRegular := by
  unfold matrixLabelReference
  exact (Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _).toOuterRegular

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_noisyObservation (m : ℕ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) :
    Tendsto (fun k : ℕ => noisyObservation m (1 / ((k : ℝ) + 1)) z)
      atTop (𝓝 (noisyObservation m 0 z)) := by
  apply Filter.Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _)

theorem projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by
  have hp : 1 < (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 < n + 1)
  have hα : 0 < 1 - 1 / ((n : ℝ) + 1) := by
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  have hC : ν Set.univ * (replicaConstant ν a m)^n ≠ ∞ := by
    unfold replicaConstant
    finiteness
  have := matrixLabelReference_outerRegular (E := E) m
  apply measure_apply_le_of_isOpen _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hC) hα
  intro U hU
  rw [← gaussianCoupling_map_noisyObservation_zero ν m]
  apply map_apply_open_le_of_tendsto (gaussianCoupling ν m)
    (matrixLabelReference (E := E) m) (noisyObservation m 0)
    (fun k => noisyObservation m (1 / ((k : ℝ) + 1)))
    (measurable_noisyObservation m 0) (fun k => measurable_noisyObservation m _)
    (tendsto_noisyObservation m) _ _ (U := U) (hU := hU)
  intro k V hV
  have hδ : (1 / ((k : ℝ) + 1)) ≠ 0 := by positivity
  rw [gaussianCoupling_map_noisyObservation ν m _ hδ]
  apply withDensity_apply_le_moment _ _
    (measurable_projectionSmoothing _ _ (measurable_gaussianPDF _ _) _) hp _ _ hV.measurableSet
  have hv : (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
      (sq_nonneg (1 / ((k : ℝ) + 1)))) ≠ 0 := by
    rw [← NNReal.coe_ne_zero]
    exact pow_ne_zero 2 hδ
  simpa only [← ENNReal.rpow_natCast, Nat.cast_add, Nat.cast_one, matrixLabelReference]
    using projectionSmoothing_moment hν hsupport
      (gaussianPDF 0 (NNReal.mk ((1 / ((k : ℝ) + 1)) ^ 2)
        (sq_nonneg (1 / ((k : ℝ) + 1))))) (measurable_gaussianPDF _ _)
      (lintegral_gaussianPDF_eq_one _ hv) m n hmargin

end ProjectionCoupling

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Support ----
namespace OAI

/-!
Finite-volume enclosures for Gaussian matrix observations.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

open scoped Pointwise

lemma coordinateNorm_sq {m : ℕ} (y : Fin m → ℝ) :
    coordinateNorm y ^ 2 = ∑ j, (y j)^2 := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 y)

lemma coordinateNorm_smul {m : ℕ} (c : ℝ) (y : Fin m → ℝ) :
    coordinateNorm (c • y) = |c| * coordinateNorm y := by
  simp [coordinateNorm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma measurableSet_coordinateBall (m : ℕ) (r : ℝ) :
    MeasurableSet (coordinateBall m r) :=
  measurableSet_le continuous_coordinateNorm.measurable measurable_const

lemma coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    coordinateBall m (c * r) = c • coordinateBall m r := by
  ext y
  constructor
  · intro hy
    refine ⟨c⁻¹ • y, ?_, by simp [hc.ne']⟩
    change coordinateNorm (c⁻¹ • y) ≤ r
    rw [coordinateNorm_smul, abs_of_pos (inv_pos.mpr hc)]
    exact (inv_mul_le_iff₀ hc).mpr hy
  · rintro ⟨y, hy, rfl⟩
    change coordinateNorm (c • y) ≤ c * r
    rw [coordinateNorm_smul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hy hc.le

lemma volume_coordinateBall_smul (m : ℕ) (c r : ℝ) (hc : 0 < c) :
    volume (coordinateBall m (c * r)) =
      ENNReal.ofReal (c^m) * volume (coordinateBall m r) := by
  rw [coordinateBall_smul m c r hc, Measure.addHaar_smul_of_nonneg volume hc.le]
  simp

lemma gaussianPDF_le_exp (x : ℝ) :
    gaussianPDF 0 1 x ≤ ENNReal.ofReal (Real.exp (-(x^2)/2)) := by
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_left (Real.exp_nonneg _)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [Real.pi_gt_three]

lemma lintegral_quarterGaussian_le :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(x^2)/4))) ≤ 4 := by
  have he : (fun x : ℝ => Real.exp (-(x^2)/4)) =
      (fun x : ℝ => Real.exp (-(1/4 : ℝ) * x^2)) := by
    ext x
    congr 1
    ring
  simp_rw [show ∀ x : ℝ, Real.exp (-(x^2)/4) = Real.exp (-(1/4 : ℝ) * x^2) from congrFun he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_mul_sq (by norm_num)) (by filter_upwards [] with x; positivity),
    integral_gaussian]
  have hs : Real.sqrt (Real.pi / (1/4 : ℝ)) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  exact (ENNReal.ofReal_le_ofReal hs).trans_eq (by norm_num)

lemma gaussian_density_pair_bound {m : ℕ} (x y : Fin m → ℝ)
    (h : coordinateNorm y ≤ coordinateNorm x) :
    (∏ j, gaussianPDF 0 1 (x j)) ≤
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
      ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
  calc
    _ ≤ ∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/2)) :=
      Finset.prod_le_prod (fun _ _ => zero_le) fun j _ => gaussianPDF_le_exp (x j)
    _ = ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2) / 2)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div, Finset.sum_neg_distrib]
    _ ≤ ENNReal.ofReal (Real.exp (- (∑ j, (x j)^2)/4 - (∑ j, (y j)^2)/4)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ coordinateNorm y := norm_nonneg _
      have hs := pow_le_pow_left₀ hn h 2
      rw [coordinateNorm_sq, coordinateNorm_sq] at hs
      linarith
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _),
        ← Real.exp_sum, ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← Real.exp_add]
      congr 2
      simp only [← Finset.sum_div, Finset.sum_neg_distrib]
      ring

lemma measurable_coordinateVolume (m : ℕ) : Measurable (fun x : Fin m → ℝ => volume (coordinateBall m (coordinateNorm x))) := by
  have : Measurable (fun z : (Fin m → ℝ) × (Fin m → ℝ) =>
      ({z | coordinateNorm z.2 ≤ coordinateNorm z.1} : Set _).indicator
        (fun _ => (1 : ℝ≥0∞)) z) :=
    measurable_const.indicator (measurableSet_le (by fun_prop) (by fun_prop))
  change Measurable (Function.uncurry (fun x y : Fin m → ℝ =>
    (coordinateBall m (coordinateNorm x)).indicator (fun _ => (1 : ℝ≥0∞)) y)) at this
  convert this.lintegral_prod_right (ν := (volume : Measure (Fin m → ℝ))) using 1
  ext x
  rw [lintegral_indicator (measurableSet_coordinateBall m _)]
  simp

lemma gaussian_expected_coordinate_volume (m : ℕ) :
    (∫⁻ x : Fin m → ℝ, volume (coordinateBall m (coordinateNorm x))
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ (16 : ℝ≥0∞)^m := by
  have hB := measurable_coordinateVolume m
  rw [pi_gaussian_withDensity m 1 (by norm_num),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hB]
  have hi (x : Fin m → ℝ) :
      (∏ j, gaussianPDF 0 1 (x j)) * volume (coordinateBall m (coordinateNorm x)) =
      ∫⁻ y : Fin m → ℝ, (coordinateBall m (coordinateNorm x)).indicator
        (fun _ => ∏ j, gaussianPDF 0 1 (x j)) y := by
    rw [lintegral_indicator (measurableSet_coordinateBall m _)]
    simp
  simp only [Pi.mul_apply]
  simp_rw [hi]
  calc
    _ ≤ ∫⁻ x : Fin m → ℝ, ∫⁻ y : Fin m → ℝ,
      (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4))) *
        ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4)) := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ coordinateBall m (coordinateNorm x)
      · rw [Set.indicator_of_mem hy]
        exact gaussian_density_pair_bound x y hy
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    _ = ((∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m)^2 := by
      have hJ : (∫⁻ y : Fin m → ℝ, ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))) =
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^m := by
        rw [volume_pi, lintegral_fin_prod volume m
          (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
        simp
      have hj (x : Fin m → ℝ) := lintegral_const_mul (μ := volume)
        (∏ j, ENNReal.ofReal (Real.exp (-(x j)^2/4)))
        (by fun_prop : Measurable (fun y : Fin m → ℝ =>
          ∏ j, ENNReal.ofReal (Real.exp (-(y j)^2/4))))
      simp_rw [hj, hJ]
      rw [lintegral_mul_const _ (by fun_prop), hJ, pow_two]
    _ ≤ ((4 : ℝ≥0∞)^m)^2 := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) lintegral_quarterGaussian_le m) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_inner_map (u : E) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) =
      gaussianReal 0 (NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖)) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ u)
  have he : (⇑(innerSL ℝ u)) = (fun x => ⟪u, x⟫) := by
    ext x
    exact innerSL_apply_apply ℝ u x
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  rw [he] at h
  have hh : (‖u‖^2).toNNReal = NNReal.mk (‖u‖^2) (sq_nonneg ‖u‖) := by
    ext
    simp
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hh] using h

lemma rows_inner_map (u : E) (m : ℕ) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map
      (fun A => fun j => ⟪u, A j⟫) =
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map
        (fun x => ‖u‖ • x) := by
  rw [Measure.pi_map_pi (f := fun _ : Fin m => fun x : E => ⟪u, x⟫)
    (fun _ => (by fun_prop : Measurable (fun x : E => ⟪u, x⟫)).aemeasurable)]
  simp_rw [stdGaussian_inner_map]
  exact (pi_gaussian_map_scale m ‖u‖).symm

lemma rows_expected_coordinate_volume (u : E) (hu : ‖u‖ ≤ 1) (m : ℕ) :
    (∫⁻ A : Fin m → E, volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))
      ∂Measure.pi (fun _ => stdGaussian E)) ≤ (16 : ℝ≥0∞)^m := by
  have h := congrArg (fun μ : Measure (Fin m → ℝ) =>
    ∫⁻ y, volume (coordinateBall m (coordinateNorm y)) ∂μ) (rows_inner_map u m)
  rw [lintegral_map (measurable_coordinateVolume m) (by fun_prop),
    lintegral_map (measurable_coordinateVolume m) (by fun_prop)] at h
  rw [h]
  apply le_trans _ (gaussian_expected_coordinate_volume m)
  apply lintegral_mono
  intro x
  apply measure_mono
  intro y hy
  change coordinateNorm y ≤ coordinateNorm x
  apply le_trans hy
  rw [coordinateNorm_smul, abs_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) hu

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowOperator_apply {m : ℕ} (A : Fin m → E) (t : E) :
    rowOperator A t = WithLp.toLp 2 (fun j => ⟪t, A j⟫) := by
  ext j
  exact real_inner_comm _ _

lemma measurableSet_netProjectionSupport (s : Finset E) (m : ℕ) :
    MeasurableSet (netProjectionSupport s m) := by
  apply MeasurableSet.biUnion s.countable_toSet
  intro u _
  exact measurableSet_le (by fun_prop) (by fun_prop)

lemma netProjectionSupport_volume (s : Finset E) (hs : ∀ u ∈ s, ‖u‖ ≤ 1) (m : ℕ) :
    matrixLabelReference (E := E) m (netProjectionSupport s m) ≤
      (s.card : ℝ≥0∞) * (32 : ℝ≥0∞)^m := by
  classical
  apply (measure_biUnion_finset_le s _).trans
  calc
    _ ≤ ∑ _u ∈ s, (32 : ℝ≥0∞)^m := by
      apply Finset.sum_le_sum
      intro u hu
      rw [matrixLabelReference, Measure.prod_apply (measurableSet_le (by fun_prop) (by fun_prop))]
      change (∫⁻ A : Fin m → E,
        volume (coordinateBall m (2 * coordinateNorm (fun j => ⟪u, A j⟫)))
        ∂Measure.pi (fun _ => stdGaussian E)) ≤ _
      simp_rw [volume_coordinateBall_smul m 2 _ (by norm_num)]
      have hme : Measurable (fun A : Fin m → E =>
          volume (coordinateBall m (coordinateNorm (fun j => ⟪u, A j⟫)))) :=
        (measurable_coordinateVolume m).comp (by fun_prop)
      rw [lintegral_const_mul _ hme]
      calc
        _ ≤ ENNReal.ofReal ((2 : ℝ)^m) * (16 : ℝ≥0∞)^m :=
          mul_le_mul' le_rfl (rows_expected_coordinate_volume u (hs u hu) m)
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num [← mul_pow]
    _ = _ := by simp
end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma opNorm_le_twice_net (f : E →L[ℝ] F) (s : Finset E)
    (hnet : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/2) :
    ‖f‖ ≤ 2 * (s.sup (fun u => ‖f u‖₊) : ℝ≥0) := by
  classical
  let K : ℝ := (s.sup (fun u => ‖f u‖₊) : ℝ≥0)
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hbound : ‖f‖ ≤ K + ‖f‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx.le
    have hfy : ‖f y‖ ≤ K := by
      exact_mod_cast (Finset.le_sup (f := fun u => ‖f u‖₊) hy)
    calc
      ‖f x‖ = ‖f y + f (x-y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖f y‖ + ‖f (x-y)‖ := norm_add_le _ _
      _ ≤ K + ‖f‖ * (1/2) := add_le_add hfy
        ((f.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_left
          (by simpa [dist_eq_norm] using hxy) (norm_nonneg _)))
      _ = _ := by ring
  dsimp [K] at hbound
  linarith
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_projection_support (m : ℕ) (hm : m ≤ Module.finrank ℝ E) :
    ∃ D : Set ((Fin m → E) × (Fin m → ℝ)), MeasurableSet D ∧
      (∀ A t, ‖t‖ ≤ 1 → (A, fun j => ⟪t, A j⟫) ∈ D) ∧
      matrixLabelReference (E := E) m D ≤ (192 : ℝ≥0∞)^(Module.finrank ℝ E) := by
  classical
  obtain ⟨s, hs, hc, hnet⟩ := exists_unit_ball_net (E := E)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hsne : s.Nonempty := by
    obtain ⟨u, hu, _⟩ := hnet 0 (by simp)
    exact ⟨u, hu⟩
  refine ⟨netProjectionSupport s m, measurableSet_netProjectionSupport s m, ?_, ?_⟩
  · intro A t ht
    obtain ⟨u, hu, he⟩ := s.exists_mem_eq_sup hsne (fun u => ‖rowOperator A u‖₊)
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨hu, ?_⟩⟩
    change coordinateNorm (fun j => ⟪t, A j⟫) ≤
      2 * coordinateNorm (fun j => ⟪u, A j⟫)
    change ‖WithLp.toLp 2 (fun j => ⟪t, A j⟫)‖ ≤
      2 * ‖WithLp.toLp 2 (fun j => ⟪u, A j⟫)‖
    rw [← rowOperator_apply, ← rowOperator_apply]
    calc
      _ ≤ ‖rowOperator A‖ * ‖t‖ := (rowOperator A).le_opNorm t
      _ ≤ ‖rowOperator A‖ := mul_le_of_le_one_right (norm_nonneg _) ht
      _ ≤ _ := by simpa [he] using opNorm_le_twice_net (rowOperator A) s hnet
  · apply (netProjectionSupport_volume s hs m).trans
    have hcard : (s.card : ℝ≥0∞) ≤ (6 : ℝ≥0∞)^(Module.finrank ℝ E) := by
      have h : (s.card : ℝ) ≤ (6 : ℝ)^(Module.finrank ℝ E) := by norm_num at hc ⊢; exact hc
      simpa using ENNReal.ofReal_le_ofReal h
    calc
      _ ≤ (6 : ℝ≥0∞)^Module.finrank ℝ E * (32 : ℝ≥0∞)^Module.finrank ℝ E :=
        mul_le_mul' hcard (pow_le_pow_right₀ (by norm_num) hm)
      _ = _ := by rw [← mul_pow]; norm_num

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Blocks ----
namespace OAI

/-!
Localization, finite selection, and block mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_univ {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    localNormalize ν a C z r univ ≤ 1 := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  simp only [localNormalize, Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z))) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (mul_le_mul' le_rfl (hν z r hr)).trans_eq (ENNReal.inv_mul_cancel hc0 hct)

omit [FiniteDimensional ℝ E] in
lemma localNormalize_finite {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure (localNormalize ν a C z r) :=
  ⟨(localNormalize_univ hν hC hCt z hr).trans_lt (by simp)⟩

omit [FiniteDimensional ℝ E] in
lemma localNormalize_support (ν : Measure E) (a : ℕ) (C : ℝ≥0∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (localNormalize ν a C z r).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, localNormalize, Measure.smul_apply, Measure.map_apply (by fun_prop)
    Metric.isClosed_closedBall.measurableSet.compl,
    Measure.restrict_apply ((by fun_prop : Measurable (fun x : E => r⁻¹ • (x-z)))
      Metric.isClosed_closedBall.measurableSet.compl)]
  have he : (fun x : E => r⁻¹ • (x-z)) ⁻¹' (Metric.closedBall 0 1)ᶜ ∩ Metric.closedBall z r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x ⟨hx,hb⟩
    apply hx
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_iff₀ hr).2 (by simpa [dist_eq_norm] using hb)
  rw [he, measure_empty, smul_zero]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_local {ν : Measure E} {a : ℕ} {C : ℝ≥0∞}
    (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    HasLocalMassBound (localNormalize ν a C z r) (a : ℝ) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  intro t _ ρ hρ
  rw [localNormalize, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  have hsub : (fun x : E => r⁻¹ • (x-z)) ⁻¹' Metric.closedBall t ρ ⊆
      Metric.closedBall (z + r • t) (r*ρ) := by
    intro x hx
    have he : x - (z+r • t) = r • (r⁻¹ • (x-z) - t) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    rw [Metric.mem_closedBall, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] using hx) hr.le
  calc
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * ν (Metric.closedBall (z+r • t) (r*ρ)) :=
      mul_le_mul' le_rfl ((Measure.restrict_le_self _).trans (measure_mono hsub))
    _ ≤ (C * ENNReal.ofReal (r^a))⁻¹ * (C * ENNReal.ofReal ((r*ρ)^a)) :=
      mul_le_mul' le_rfl (hν _ _ (mul_pos hr hρ))
    _ = ENNReal.ofReal (ρ^(a : ℝ)) := by
      rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le a), ← mul_assoc C,
        ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul, Real.rpow_natCast]

lemma projectionLaw_uniform_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} (hν : HasLocalMassBound ν (a : ℝ)) (hν1 : ν univ ≤ 1)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E)
    (hn : 1 ≤ n) (hmargin : n+m ≤ a) (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ)+1)) := by
  apply (projectionLaw_set_bound hν hsupport m n hn (by exact_mod_cast hmargin) S).trans
  apply mul_le_mul' _ le_rfl
  have hn0 : (0 : ℝ) < n+1 := by positivity
  calc
    _ ≤ (((128 : ℝ≥0∞)^Module.finrank ℝ E) ^ n)^(1 / ((n : ℝ)+1)) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      simpa only [one_mul] using mul_le_mul' hν1 (pow_le_pow_left' (replicaConstant_le hν1 hd ha hm) n)
    _ = ((128 : ℝ≥0∞)^Module.finrank ℝ E)^((n : ℝ)/(n+1)) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      rw [mul_one_div]
    _ ≤ ((128 : ℝ≥0∞)^Module.finrank ℝ E)^(1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        ((div_le_one hn0).2 (by linarith))
    _ = _ := ENNReal.rpow_one _

lemma finite_rpow_holder {J : Type*} [Fintype J] (a : J → ℝ≥0∞) {q : ℝ} (hq : 1 < q) :
    (∑ j, a j ^ (1 - 1/q)) ≤
      (Fintype.card J : ℝ≥0∞)^(1/q) * (∑ j, a j)^(1-1/q) := by
  have hh := Real.HolderConjugate.conjExponent hq
  have hq' : q.conjExponent ≠ 0 := ne_of_gt hh.symm.pos
  have hex : 1 - 1/q = q.conjExponent⁻¹ := by simpa only [one_div] using hh.one_sub_inv
  rw [hex]
  simpa only [one_mul, one_div, ENNReal.one_rpow, ENNReal.rpow_inv_rpow hq',
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    ENNReal.inner_le_Lp_mul_Lq Finset.univ (fun _ : J => (1 : ℝ≥0∞))
      (fun j => a j ^ q.conjExponent⁻¹) hh

lemma normalized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} (hν : ∀ j, HasLocalMassBound (ν j) (a : ℝ))
    (hν1 : ∀ j, ν j univ ≤ 1) (hsupport : ∀ j, (ν j).support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ) :
    (∑ j, projectionLaw (ν j) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) := by
  classical
  obtain ⟨D, hD, hDs, hDV⟩ := exists_projection_support (E := E) m hm
  let S : J → Set ((Fin m → E) × (Fin m → ℝ)) := fun j => D ∩ {x | φ x = j}
  have hS (j : J) : MeasurableSet (S j) := hD.inter (hφ (measurableSet_singleton j))
  have hSD (j : J) : projectionLaw (ν j) m (S j) = projectionLaw (ν j) m {x | φ x = j} := by
    apply Measure.measure_inter_eq_of_ae
    unfold projectionLaw
    apply (ae_map_iff (by fun_prop) hD).2
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ν j).support_mem_ae] with x hx
    exact hDs x.1 x.2 (by simpa using hsupport j hx)
  have hdis : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hUnion : (⋃ j, S j) = D := by
    ext x
    simp only [S, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_,h,_⟩ => h, fun h => ⟨φ x,h,rfl⟩⟩
  have hsum : ∑ j, matrixLabelReference (E := E) m (S j) = matrixLabelReference (E := E) m D := by
    simpa only [hUnion, tsum_fintype] using (measure_iUnion (μ := matrixLabelReference (E := E) m) hdis hS).symm
  have hα : 0 ≤ 1 - 1/((n : ℝ)+1) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ n+1)]
  have hV : (matrixLabelReference (E := E) m D)^(1-1/((n : ℝ)+1)) ≤
      (256 : ℝ≥0∞)^Module.finrank ℝ E := by
    calc
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^(1-1/((n : ℝ)+1)) :=
        ENNReal.rpow_le_rpow (hDV.trans (pow_le_pow_left' (by norm_num) _)) hα
      _ ≤ ((256 : ℝ≥0∞)^Module.finrank ℝ E)^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (sub_le_self _ (by positivity))
      _ = _ := ENNReal.rpow_one _
  calc
    _ = ∑ j, projectionLaw (ν j) m (S j) := by simp_rw [hSD]
    _ ≤ ∑ j, (128 : ℝ≥0∞)^Module.finrank ℝ E *
        (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) :=
      Finset.sum_le_sum fun j _ => projectionLaw_uniform_set_bound
        (hν j) (hν1 j) (hsupport j) hd ha hm hn hmargin (S j)
    _ = (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ∑ j, (matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1)) := by rw [Finset.mul_sum]
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
         (∑ j, matrixLabelReference (E := E) m (S j))^(1-1/((n : ℝ)+1))) :=
      mul_le_mul' le_rfl (finite_rpow_holder _ (by exact_mod_cast Nat.lt_add_one_of_le hn))
    _ ≤ (128 : ℝ≥0∞)^Module.finrank ℝ E *
        ((Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * (256 : ℝ≥0∞)^Module.finrank ℝ E) := by
      rw [hsum]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hV)
    _ = _ := by rw [mul_left_comm, ← mul_pow]; norm_num; rw [mul_comm]

omit [FiniteDimensional ℝ E] in
lemma localNormalize_reconstruct (ν : Measure E) (a : ℕ) {C : ℝ≥0∞}
    (hC : C ≠ 0) (hCt : C ≠ ∞) (z : E) {r : ℝ} (hr : 0 < r) :
    (C * ENNReal.ofReal (r^a)) • (localNormalize ν a C z r).map (fun t => z+r • t) =
      ν.restrict (Metric.closedBall z r) := by
  have hc0 : C * ENNReal.ofReal (r^a) ≠ 0 := mul_ne_zero hC (by positivity)
  have hct : C * ENNReal.ofReal (r^a) ≠ ∞ := ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  rw [localNormalize, Measure.map_smul, smul_smul, ENNReal.mul_inv_cancel hc0 hct,
    one_smul, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun t : E => z+r • t) ∘ (fun x => r⁻¹ • (x-z)) = id := by
    ext x
    simp [smul_smul, hr.ne']
  rw [he, Measure.map_id]

lemma projectionLaw_smul (ν : Measure E) [SFinite ν] (m : ℕ) (c : ℝ≥0∞) :
    projectionLaw (c • ν) m = c • projectionLaw ν m := by
  rw [projectionLaw, Measure.prod_smul_right, Measure.map_smul]
  rfl

lemma projectionLaw_affine (ν : Measure E) [SFinite ν] (m : ℕ) (z : E) (r : ℝ) :
    projectionLaw (ν.map (fun t => z + r • t)) m =
      (projectionLaw ν m).map (fun x => (x.1, fun j => ⟪z,x.1 j⟫ + r * x.2 j)) := by
  unfold projectionLaw
  rw [← Measure.map_id (μ := Measure.pi (fun _ : Fin m => stdGaussian E)),
    Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_id, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x <;> simp [inner_add_left, real_inner_smul_left]

lemma localized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : ∀ j, PolynomialMass (ν j) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ)
    (z : E) {r : ℝ} (hr : 0 < r) :
    (∑ j, projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) *
        C * ENNReal.ofReal (r^a) := by
  let τ (j : J) := localNormalize (ν j) a C z r
  let F : ((Fin m → E) × (Fin m → ℝ)) → ((Fin m → E) × (Fin m → ℝ)) :=
    fun x => (x.1, fun i => ⟪z,x.1 i⟫ + r * x.2 i)
  have hF : Measurable F := by fun_prop
  let (j : J) : IsFiniteMeasure (τ j) := localNormalize_finite (hν j) hC hCt z hr
  have hb := normalized_routing_bound τ
    (fun j => localNormalize_local (hν j) hC hCt z hr)
    (fun j => localNormalize_univ (hν j) hC hCt z hr)
    (fun j => localNormalize_support (ν j) a C z hr) hd ha hm hn hmargin (φ ∘ F) (hφ.comp hF)
  have he (j : J) : projectionLaw ((ν j).restrict (Metric.closedBall z r)) m {x | φ x = j} =
      (C * ENNReal.ofReal (r^a)) * projectionLaw (τ j) m {x | φ (F x) = j} := by
    rw [← localNormalize_reconstruct (ν j) a hC hCt z hr, projectionLaw_smul,
      projectionLaw_affine, Measure.smul_apply, smul_eq_mul, Measure.map_apply hF
      (measurableSet_eq_fun hφ measurable_const)]
    rfl
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul' le_rfl hb).trans_eq (by ring)

lemma projectionLaw_withDensity_apply (μ : Measure E) [SFinite μ] {h : E → ℝ≥0∞}
    (hh : Measurable h) [SFinite (μ.withDensity h)] (m : ℕ)
    {S : Set ((Fin m → E) × (Fin m → ℝ))} (hS : MeasurableSet S) :
    projectionLaw (μ.withDensity h) m S =
      ∫⁻ s, h s * (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (A, fun j => ⟪s,A j⟫)
        ∂Measure.pi (fun _ : Fin m => stdGaussian E)) ∂μ := by
  have hobs : Measurable (fun x : (Fin m → E) × E => (x.1, fun j => ⟪x.2,x.1 j⟫)) := by fun_prop
  have hi : Measurable (fun x : (Fin m → E) × E => S.indicator (fun _ => (1 : ℝ≥0∞))
      (x.1, fun j => ⟪x.2,x.1 j⟫)) :=
    ((measurable_const : Measurable (fun _ => (1 : ℝ≥0∞))).indicator hS).comp hobs
  rw [projectionLaw, Measure.map_apply hobs hS]
  rw [← one_mul (((Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) _),
    ← lintegral_indicator_const (hobs hS) 1]
  change (∫⁻ x : (Fin m → E) × E, S.indicator (fun _ => (1 : ℝ≥0∞))
    (x.1, fun j => ⟪x.2,x.1 j⟫) ∂(Measure.pi (fun _ : Fin m => stdGaussian E)).prod (μ.withDensity h)) = _
  rw [lintegral_prod_symm _ hi.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul μ hh hi.lintegral_prod_left]
  rfl

lemma blockValue_mass_identity (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {m : ℕ} {h : J → E → ℝ≥0∞} (hh : ∀ j, Measurable (h j))
    (hh1 : ∀ j s, h j s ≤ 1)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ)
    {S : Set E} (hS : MeasurableSet S) :
    (μ.withDensity (blockValue h φ)) S =
      ∑ j, projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} := by
  classical
  let g (j : J) (s : E) (A : Fin m → E) : ℝ≥0∞ :=
    if φ (A, fun k => ⟪s,A k⟫) = j then h j s else 0
  have hg (j : J) : Measurable (Function.uncurry (g j)) := by
    exact Measurable.ite (measurableSet_eq_fun (hφ.comp (by fun_prop)) measurable_const)
      ((hh j).comp measurable_fst) measurable_const
  have hselect (s : E) (A : Fin m → E) : h (φ (A, fun k => ⟪s,A k⟫)) s = ∑ j, g j s A := by
    simp [g]
  have he (j : J) : projectionLaw ((μ.withDensity (h j)).restrict S) m {x | φ x = j} =
      ∫⁻ s in S, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
    rw [restrict_withDensity hS]
    let : IsFiniteMeasure ((μ.restrict S).withDensity (h j)) :=
      isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
    rw [projectionLaw_withDensity_apply _ (hh j) _ (measurableSet_eq_fun hφ measurable_const)]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ (ne_of_lt ((hh1 j s).trans_lt (by simp)))]
    apply lintegral_congr
    intro A
    by_cases hx : φ (A, fun k => ⟪s,A k⟫) = j <;> simp [g, hx]
  rw [withDensity_apply _ hS]
  calc
    _ = ∫⁻ s in S, ∑ j, ∫⁻ A, g j s A ∂Measure.pi (fun _ : Fin m => stdGaussian E) ∂μ := by
      apply lintegral_congr
      intro s
      unfold blockValue
      simp_rw [hselect]
      exact lintegral_finsetSum _ (fun j _ => (hg j).comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      rw [lintegral_finsetSum _ (fun j _ => (hg j).lintegral_prod_right)]
      simp_rw [he]

lemma blockValue_mass_bound (μ : Measure E) [IsFiniteMeasure μ]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {a m n : ℕ} {C : ℝ≥0∞} {h : J → E → ℝ≥0∞}
    (hh : ∀ j, Measurable (h j)) (hh1 : ∀ j s, h j s ≤ 1)
    (hlocal : ∀ j, PolynomialMass (μ.withDensity (h j)) a C)
    (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    {φ : ((Fin m → E) × (Fin m → ℝ)) → J} (hφ : Measurable φ) :
    PolynomialMass (μ.withDensity (blockValue h φ)) a
      ((32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) * C) := by
  let (j : J) : IsFiniteMeasure (μ.withDensity (h j)) :=
    isFiniteMeasure_withDensity (ne_of_lt ((lintegral_mono (hh1 j)).trans_lt (by simp)))
  intro z r hr
  rw [blockValue_mass_identity μ hh hh1 hφ Metric.isClosed_closedBall.measurableSet]
  exact localized_routing_bound (fun j => μ.withDensity (h j)) hlocal hC hCt hd ha hm hn hmargin φ hφ z hr

end Block

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Stream ----
namespace OAI

/-!
Sequential routing and continuation mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_cons (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f v ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ v : Fin n → E, f (Fin.cons x v) ∂Measure.pi (fun _ => ν) ∂ν := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (0 : Fin (n+1))).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f, lintegral_prod]
  · congr 1
    ext x
    congr 1
    ext v
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp
  · exact (hf.comp hp.measurable).aemeasurable

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) => streamRoute δ (n+1) k (δ (n+1) j (x.1 0,x.2 0)) (Fin.tail x.1,Fin.tail x.2))
    have ht : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        (Fin.tail x.1, Fin.tail x.2)) := by
      change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        ((fun i : Fin k => x.1 i.succ), (fun i : Fin k => x.2 i.succ)))
      fun_prop
    have hd : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        δ (n+1) j (x.1 0,x.2 0)) := (hδ (n+1) j).comp (by fun_prop)
    exact measurable_select (fun a => (ih (n+1) a).comp ht) hd

lemma measurable_continuation {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : J) :
    Measurable (continuation δ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact measurable_select (fun a => (ih (n+1) a).comp measurable_snd)
      ((hδ (n+1) j).comp (by fun_prop))

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma continuation_le_one {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : E) :
    continuation δ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    refine (lintegral_mono (fun x => ih _ _)).trans_eq ?_
    rw [lintegral_const, one_mul, stdGaussian,
      Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ

lemma continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by
  induction m generalizing n j with
  | zero =>
    simp [blockValue, streamRoute]
  | succ m ih =>
    rw [Nat.succ_add, continuation]
    simp_rw [ih]
    unfold blockValue
    have hf : Measurable (fun A : Fin (m+1) → E =>
        continuation δ w (n+(m+1)) k (streamRoute δ n (m+1) j (A,fun i => ⟪s,A i⟫)) s) := by
      exact (measurable_of_finite (fun a => continuation δ w (n+(m+1)) k a s)).comp
        ((measurable_streamRoute hδ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro A
    have he : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x A : Fin (m+1) → E) i⟫) = (fun i => ⟪s,A i⟫) := by
      ext i
      simp [Fin.tail]
    simp [streamRoute, he, Nat.add_left_comm, Nat.add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamFactor_ne_top (q : ℕ) : streamFactor (E := E) (J := J) q ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

end StreamAux

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Stopping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma continuation_mass_bound_ceil [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ ((k+q-1)/q)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q),pow_zero,mul_one,continuation] using hlocal n j
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q+q-1)/q) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q+q-1)/q) ≠ ∞ :=
        ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
      have hb := blockValue_mass_bound μ
        (fun b => measurable_continuation hδ hw (n+q) (k-q) b)
        (fun b s => continuation_le_one hw1 (n+q) (k-q) b s)
        (fun b => ih (k-q) hki (n+q) b) hC1 hC1t hd ha
        (by omega : q ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+q ≤ a) (measurable_streamRoute hδ n q j)
      have he : continuation δ w n k j =
          blockValue (fun b => continuation δ w (n+q) (k-q) b) (streamRoute δ n q j) := by
        funext s
        simpa [Nat.add_sub_of_le hk] using continuation_unroll hδ n q (k-q) j s
      rw [he]
      have hdiv : (k+q-1)/q = (k-q+q-1)/q+1 := by
        have he : k+q-1 = q+(k-q+q-1) := by omega
        rw [he,Nat.add_div_left _ hq0]
      convert hb using 1
      rw [hden, ← streamFactor, hdiv, pow_succ]
      ring
    · have hkm : k ≤ q := by omega
      have hb := blockValue_mass_bound μ
        (fun b => hw (n+k) b) (fun b s => hw1 (n+k) b s) (hlocal (n+k)) hC hCt hd ha
        (by omega : k ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+k ≤ a) (measurable_streamRoute hδ n k j)
      have he : continuation δ w n k j = blockValue (w (n+k)) (streamRoute δ n k j) := by
        funext s
        simpa [continuation] using continuation_unroll hδ n k 0 j s
      rw [he]
      convert hb using 1
      have hdiv : (k+q-1)/q = 1 := by
        have he : k+q-1 = q+(k-1) := by omega
        rw [he,Nat.add_div_left _ hq0,Nat.div_eq_of_lt (by omega : k-1 < q)]
      rw [hden, ← streamFactor,hdiv,pow_one]
      exact mul_comm _ _

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

end Learner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.NoiselessRegression.continuation_mass_bound_ceil := @_root_.OAI.NoiselessRegression.continuation_mass_bound_ceil
