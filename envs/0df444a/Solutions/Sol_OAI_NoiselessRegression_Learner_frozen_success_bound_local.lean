-- Prove2me | solution 1 for OAI.NoiselessRegression.Learner.frozen_success_bound_local
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:29:55.070363+00:00
-- url     : https://prove2.me/submissions/ffaf22f6-f306-4f69-9b50-ae0883f8b4a4

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Streaming.lean:L284-L333
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.Learner.frozen_success_bound_local. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Theorems.Thm_OAI_NoiselessRegression_Learner_stoppedContinuation_mass_bound
import Theorems.Thm_OAI_NoiselessRegression_capWeight_mass_mixed
import Theorems.Thm_OAI_NoiselessRegression_card_le_volume_ratio
import Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound
import Theorems.Thm_OAI_NoiselessRegression_projectionLaw_absolutelyContinuous

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

end AffineTubes

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Sphere ----
namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma unitBallLaw_closedBall (z : E) {r : ℝ} (hr : 0 < r) :
    unitBallLaw (Metric.closedBall z r) ≤ ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
  have h0 : (volume : Measure E) (Metric.ball 0 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have ht : (volume : Measure E) (Metric.ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  calc
    _ ≤ ((volume : Measure E) (Metric.ball 0 1))⁻¹ * volume (Metric.closedBall z r) := by
      exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = _ := by
      rw [Measure.addHaar_closedBall _ _ hr.le, mul_comm _ (_ * _), mul_assoc,
        ENNReal.mul_inv_cancel h0 ht, mul_one]

lemma unitBallLaw_local : HasLocalMassBound (unitBallLaw : Measure E)
    (Module.finrank ℝ E : ℝ) := by
  intro z _ r hr
  simpa only [Real.rpow_natCast] using unitBallLaw_closedBall z hr

lemma unitBallLaw_support : (unitBallLaw : Measure E).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]
  simp

lemma sphereLaw_apply [Nontrivial E] {s : Set (Metric.sphere (0 : E) 1)}
    (hs : MeasurableSet s) :
    sphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  have hd0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hdt : (Module.finrank ℝ E : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s) ⊆ Metric.closedBall (0 : E) 1 := by
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      (mem_sphere_zero_iff_norm.mp x.property), mul_one, Real.norm_eq_abs,
      abs_of_pos hr.1]
    exact hr.2.le
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul, Measure.toSphere_apply_univ,
    Measure.toSphere_apply' _ hs, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdt), unitBallLaw, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Set.inter_eq_left.mpr hsub]
  calc
    _ = ((volume : Measure E) (Metric.ball 0 1))⁻¹ *
      (((Module.finrank ℝ E : ℝ≥0∞))⁻¹ * (Module.finrank ℝ E)) *
      volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hd0 hdt, mul_one]

lemma sphereLaw_cap_raw [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) :
    sphereLaw {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r} ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) *
        ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) := by
  classical
  let L := (Submodule.span ℝ ({z} : Set E)).toAffineSubspace
  let : Nonempty L := ⟨⟨0, (Submodule.span ℝ ({z} : Set E)).zero_mem⟩⟩
  have hl : Module.finrank ℝ L.direction ≤ 1 := by
    dsimp only [L]
    rw [Submodule.toAffineSubspace_direction]
    simpa using (finrank_span_le_card (R := ℝ) ({z} : Set E))
  have hm : (Module.finrank ℝ L.direction : ℝ) + (Module.finrank ℝ E - 1 : ℕ) ≤
      (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (by omega : Module.finrank ℝ L.direction + (Module.finrank ℝ E - 1) ≤ Module.finrank ℝ E)
  have hsub : Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' {s : Metric.sphere (0 : E) 1 | dist s.val z ≤ r}) ⊆
      {t | Metric.infDist t L ≤ r} := by
    rintro _ ⟨c, hc, _, ⟨s, hs, rfl⟩, rfl⟩
    have hz : c • z ∈ L := Submodule.smul_mem _ c (Submodule.subset_span (by simp))
    exact (Metric.infDist_le_dist_of_mem hz).trans (by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hc.1]
      exact (mul_le_mul_of_nonneg_left hs hc.1.le).trans (mul_le_of_le_one_left hr.le hc.2.le))
  rw [sphereLaw_apply (measurableSet_le (by fun_prop) measurable_const)]
  apply (measure_mono hsub).trans
  apply (unitBallLaw_local.affine_tube_pow unitBallLaw_support L _ hm hr hr1).trans
  simp only [Real.rpow_natCast]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hl)
    (by positivity)

end SphereBounds

open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma ambientSphereLaw_support : (ambientSphereLaw (E := E)).support ⊆ Metric.sphere 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_sphere
  rw [mem_ae_iff, ambientSphereLaw, Measure.map_apply (by fun_prop)
    Metric.isClosed_sphere.measurableSet.compl]
  have h : (Subtype.val : Metric.sphere (0 : E) 1 → E) ⁻¹' (Metric.sphere 0 1)ᶜ = ∅ := by
    ext x
    simp
  rw [h, measure_empty]

lemma ambientSphereLaw_closedBall [Nontrivial E] (z : E) {r : ℝ} (hr : 0 < r)
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E - 1) :
    ambientSphereLaw (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3 : ℝ) * 4 ^ Module.finrank ℝ E) * ENNReal.ofReal (r^k) := by
  by_cases hr1 : r ≤ 1
  · rw [ambientSphereLaw, Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
    apply (sphereLaw_cap_raw z hr hr1 (Module.finrank_pos (R := ℝ) (M := E))).trans
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr.le hr1 hk)
  · have hr1 : 1 ≤ r := (le_of_not_ge hr1)
    calc
      _ ≤ 1 := prob_le_one
      _ ≤ _ := by
        apply one_le_mul
        · rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          have : (1 : ℝ) ≤ 4 ^ Module.finrank ℝ E := one_le_pow₀ (by norm_num)
          linarith
        · rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hr1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma chord_le_arccos (s t : Metric.sphere (0 : E) 1) :
    dist s.val t.val ≤ Real.arccos ⟪s.val,t.val⟫ := by
  have hs : ‖s.val‖ = 1 := mem_sphere_zero_iff_norm.mp s.property
  have ht : ‖t.val‖ = 1 := mem_sphere_zero_iff_norm.mp t.property
  have habs : |⟪s.val,t.val⟫| ≤ 1 := by
    simpa [hs, ht] using abs_real_inner_le_norm s.val t.val
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪s.val,t.val⟫)
  rw [Real.cos_arccos (abs_le.mp habs).1 (abs_le.mp habs).2] at hcos
  have hd : (dist s.val t.val)^2 = 2 - 2*⟪s.val,t.val⟫ := by
    rw [dist_eq_norm, norm_sub_sq_real, hs, ht]
    ring
  nlinarith [dist_nonneg (x := s.val) (y := t.val), Real.arccos_nonneg ⟪s.val,t.val⟫]

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Observation ----
namespace OAI

/-!
Absolute continuity of noiseless spherical observation laws.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by
  have hac : projectionLaw (ambientSphereLaw (E := E)) 1 ≪ matrixLabelReference (E := E) 1 := by
    apply projectionLaw_absolutelyContinuous (a := 2) (n := 1)
      (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
    · intro z r hr
      exact ambientSphereLaw_closedBall z hr 2 (by omega)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → E) × E => (z.1, fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian E)).prod (ambientSphereLaw (E := E)))
      (matrixLabelReference (E := E) 1) := ⟨by fun_prop, hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian E) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) E)).prod
    (measurable_subtype_coe.measurePreserving (sphereLaw (E := E)))
  have h2 := (measurePreserving_funUnique (stdGaussian E) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  ext z <;> simp [MeasurableEquiv.funUnique]

end ObservationAC

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

lemma fin_tail_snoc {X : Type*} {k : ℕ} (A : Fin (k+1) → X) (x : X) :
    Fin.tail (Fin.snoc A x : Fin (k+2) → X) =
      (Fin.snoc (Fin.tail A : Fin k → X) x : Fin (k+1) → X) := by
  rw [← Fin.cons_self_tail A, ← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons, Fin.tail_cons]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_snoc (δ : ℕ → J → (E × ℝ) → J) (n k : ℕ) (j : J)
    (A : Fin k → E) (b : Fin k → ℝ) (x : E) (y : ℝ) :
    streamRoute δ n (k+1) j (Fin.snoc A x, Fin.snoc b y) =
      δ (n+k+1) (streamRoute δ n k j (A,b)) (x,y) := by
  induction k generalizing n j with
  | zero => simp [streamRoute, Fin.snoc_zero]
  | succ k ih =>
    rw [streamRoute]
    simp only [Fin.snoc_apply_zero, fin_tail_snoc]
    rw [ih, streamRoute]
    congr 1; omega

end StreamAux

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Execution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite-state sequential execution and terminal-state witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

lemma fin_prefix_snoc {X : Type*} {n T : ℕ} (h : n+1 ≤ T) (x : Fin T → X) :
    (fun i : Fin (n+1) => x (Fin.castLE h i)) =
      (Fin.snoc (fun i : Fin n => x (Fin.castLE (by omega) i))
        (x ⟨n, by omega⟩) : Fin (n+1) → X) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rfl
  · simp

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

end Learner

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Transfer ----
namespace OAI

/-!
Prefix integration and transfer between almost-everywhere equal transitions.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma streamRoute_congr {J : Type*} (δ δ' : ℕ → J → (E × ℝ) → J)
    (n k : ℕ) (j : J) (A : Fin k → E) (b : Fin k → ℝ)
    (h : ∀ t j i, δ t j (A i,b i) = δ' t j (A i,b i)) :
    streamRoute δ n k j (A,b) = streamRoute δ' n k j (A,b) := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    rw [streamRoute, streamRoute, h]
    exact ih (n+1) _ (Fin.tail A) (Fin.tail b) (fun t j i => h t j i.succ)

end StreamTransfer

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Stopping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

lemma decode_taggedStart (a : Bool × State M) :
    decodeTagged (taggedStart (T := T) a) = if a.1 then .inr (0,a.2) else .inl a.2 := by
  simp only [taggedStart]; split_ifs <;> rfl

lemma run_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.run s ω x n = decodeTagged (streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j))
      0 n (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE hn i)),fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫),streamRoute_snoc]
    rw [run,ih (by omega)]
    generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 n
      (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE (by omega : n ≤ T) i)),fun i => ⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫) = j
    cases j with
    | inr done => rfl
    | inl j =>
      simp only [decodeTagged, taggedStep, Nat.zero_add,dite_eq_left (by omega : n < T),
        dite_eq_left (by omega : n+1 ≤ T),real_inner_comm]
      split_ifs <;> rfl

lemma estimate_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    L.estimate s ω x = L.taggedOutput ω (streamRoute
      (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T (taggedStart (L.initialChoice ω))
      (x,fun i => ⟪s.val,x i⟫)) := by
  unfold estimate terminal
  rw [L.run_eq_taggedRoute s ω x le_rfl]
  have hi : (fun i : Fin T => x (Fin.castLE le_rfl i)) = x := by funext i; exact congrArg x (Fin.ext rfl)
  have hb : (fun i : Fin T => ⟪s.val,x (Fin.castLE le_rfl i)⟫) = (fun i => ⟪s.val,x i⟫) := by funext i; rfl
  rw [hi,hb]
  generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T
    (taggedStart (L.initialChoice ω)) (x,fun i => ⟪s.val,x i⟫) = j
  cases j with
  | inl j => rfl
  | inr done => rfl

lemma taggedStep_congr {τ τ' : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ)
    (h : ∀ a, τ t a obs = τ' t a obs) :
    taggedStep τ t j obs = taggedStep τ' t j obs := by
  cases j with
  | inr done => rfl
  | inl j => simp only [taggedStep,h]

end Learner
end NoiselessRegression

end

end OAI

-- ---- inlined from the OAI_NoiselessRegression_Learner_continuation_tagged_eq solution (the platform cannot check that node's statement) ----
-- ---- from OAI.Probability.ProjectionMoments.StoppingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end

namespace Learner

section
variable {d M : ℕ}

end

variable {d M T : ℕ}

lemma continuation_tagged_eq {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (n k : ℕ) (hnk : n+k ≤ T) (j : TaggedState M T) (s : Vector d) :
    continuation (taggedStep τ) (taggedWeight w) n k j s =
      match j with
      | .inl a => stoppedContinuation τ w n k a s
      | .inr (t,a) => w t a s := by
  induction k generalizing n j with
  | zero => cases j <;> rfl
  | succ k ih =>
    cases j with
    | inl j =>
      simp only [continuation,stoppedContinuation]
      apply lintegral_congr
      intro x
      rw [ih (n+1) (by omega)]
      simp only [taggedStep,dite_eq_left (by omega : n+1 ≤ T)]
      split_ifs <;> rfl
    | inr done =>
      simp only [continuation,taggedStep]
      simp only [ih (n+1) (by omega),lintegral_const,measure_univ,mul_one]

variable [NeZero d]

end Learner
end NoiselessRegression

end

end OAI

-- ---- inlined from the OAI_NoiselessRegression_Learner_stopped_route_mixed_bound solution (the platform cannot check that node's statement) ----
-- ---- from OAI.Probability.GaussianRegression.Sphere ----
namespace OAI

/-!
Normalized spherical surface measure, cap bounds, and rotational symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

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
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

end StreamAux

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.GaussianRegression.Caps ----
namespace OAI

/-!
Spherical cap mass bounds along sequential routes.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] in
lemma measurable_capWeight (y : E) (ε : ℝ) : Measurable (capWeight y ε) :=
  measurable_const.indicator Metric.isClosed_closedBall.measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma capWeight_le_one (y s : E) (ε : ℝ) : capWeight y ε s ≤ 1 := by
  classical
  simp only [capWeight, Set.indicator_apply]
  split <;> simp

lemma ambient_mass_bound {f : E → ℝ≥0∞} {a : ℕ} {C : ℝ≥0∞}
    (h : PolynomialMass ((ambientSphereLaw (E := E)).withDensity f) a C) :
    (∫⁻ s, f s ∂ambientSphereLaw) ≤ C := by
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  apply (measure_mono_ae ?_).trans (by simpa using h 0 1 zero_lt_one)
  filter_upwards [(withDensity_absolutelyContinuous (ambientSphereLaw (E := E)) f).ae_le
    (ambientSphereLaw_ae_norm (E := E))] with s hs
  intro _
  change dist s 0 ≤ 1
  simp [dist_zero_right, hs]

end StreamCaps

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

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

lemma measurable_taggedStep {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (t : ℕ) (j : TaggedState M T) :
    Measurable (taggedStep (T := T) τ t j) := by
  classical
  cases j with
  | inr done => exact measurable_const
  | inl j =>
    unfold taggedStep
    split_ifs with ht
    · exact (measurable_of_finite (fun a : Bool × State M =>
        if a.1 then Sum.inr ((⟨t,by omega⟩ : Fin (T+1)),a.2) else Sum.inl a.2)).comp (hτ t j)
    · exact measurable_const

end Learner
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.StoppingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end

namespace Learner

section
variable {d M : ℕ}

end

variable {d M T : ℕ}

lemma measurable_taggedWeight {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j, Measurable (w n j)) (n : ℕ) (j : TaggedState M T) :
    Measurable (taggedWeight w n j) := by cases j <;> exact hw _ _

lemma tagged_continuation_mass {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (ambientSphereLaw.withDensity (w n j)) a C)
    (hd : 1 ≤ d) (ha : a ≤ d) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (j : TaggedState M T) :
    PolynomialMass (ambientSphereLaw.withDensity
      (continuation (taggedStep τ) (taggedWeight w) 0 T j)) a
      (C * streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q)) := by
  have he := fun s => continuation_tagged_eq (τ := τ) (w := w) 0 T (by omega) j s
  cases j with
  | inl j =>
    have he' : continuation (taggedStep (T := T) τ) (taggedWeight w) 0 T (.inl j) = stoppedContinuation τ w 0 T j :=
      funext he
    rw [he']
    exact stoppedContinuation_mass_bound hτ hw hw1 hC hCt hlocal hd ha hq hqa 0 T j
  | inr done =>
    have he' : continuation (taggedStep (T := T) τ) (taggedWeight w) 0 T (.inr done) = w done.1 done.2 :=
      funext he
    rw [he']
    intro z r hr
    apply (hlocal _ _ z r hr).trans
    apply mul_le_mul' _ le_rfl
    exact le_mul_of_one_le_right' (one_le_pow₀ (one_le_streamFactor (by omega)))

variable [NeZero d]

lemma stopped_route_mixed_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (y : ℕ → State M → Vector d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (j : TaggedState M T) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | dist z.1.val
        (match streamRoute (taggedStep (T := T) τ) 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
        | .inl a => y T a
        | .inr (t,a) => y t a) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  let w : ℕ → State M → Vector d → ℝ≥0∞ := fun n j => capWeight (y n j) ε
  let δ := taggedStep (T := T) τ
  let w' : ℕ → TaggedState M T → Vector d → ℝ≥0∞ := taggedWeight w
  let yy : TaggedState M T → Vector d := fun a => match a with
    | .inl a => y T a
    | .inr (t,a) => y t a
  have hw' (n : ℕ) (a : TaggedState M T) : Measurable (w' n a) :=
    measurable_taggedWeight (fun n j => measurable_capWeight _ _) n a
  have hδ := measurable_taggedStep (T := T) hτ
  have hV := measurable_continuation hδ hw' 0 T j
  have he (s : Vector d) : continuation δ w' 0 T j s =
      ∫⁻ A : Fin T → Vector d, capWeight (yy (streamRoute δ 0 T j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian (Vector d)) := by
    have hu := continuation_unroll (w := w') hδ 0 T 0 j s
    simp only [Nat.add_zero,continuation] at hu
    rw [hu]
    unfold blockValue
    apply lintegral_congr
    intro A
    cases streamRoute δ 0 T j (A,fun i => ⟪s,A i⟫) <;> simp [w',w,yy,taggedWeight]
  let S : Set (UnitSphere d × Samples d T) :=
    {z | dist z.1.val (yy (streamRoute δ 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite yy).comp ((measurable_streamRoute hδ 0 T j).comp (by fun_prop)))
  change ((sphereLaw (E := Vector d)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := Vector d)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : UnitSphere d,
      (∫⁻ A, S.indicator (fun _ => (1:ℝ≥0∞)) (s,A) ∂sampleLaw d T) = continuation δ w' 0 T j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (yy (streamRoute δ 0 T j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  apply ambient_mass_bound (a := a)
  have ha : a ≤ d := by
    have hdn : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
    have : (a:ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hl (n : ℕ) (j : State M) : PolynomialMass (ambientSphereLaw.withDensity (w n j)) a
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) := by
    simpa only [finrank_euclideanSpace_fin] using capWeight_mass_mixed (y n j) hε hε1 a hb (by simpa using hab)
  exact tagged_continuation_mass hτ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    hl
    (Nat.pos_of_ne_zero (NeZero.ne d)) ha hq hqa j

end Learner
end NoiselessRegression

end

end OAI


-- ---- from OAI.Probability.ProjectionMoments.Streaming ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
namespace Learner
universe u

end Learner

universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

namespace Learner
variable {d M T : ℕ} {Ω : Type u}

end Learner
end

namespace Learner

section
universe u

end

universe u
variable {d M T : ℕ} {Ω : Type u}

lemma frozen_success_bound_local (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (L.transition t ω j) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ)) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let τ : ℕ → State M → (Vector d × ℝ) → Bool × State M := fun t j => (htrans t j).mk _
  have hτ (t : ℕ) (j : State M) : Measurable (τ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫) = τ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S := {z : UnitSphere d × Samples d T | dist z.1.val
    (L.taggedOutput ω (streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
      (z.2,fun i => ⟪z.1.val,z.2 i⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    intro hs
    have he := streamRoute_congr (taggedStep (T := T) (fun t j => L.transition t ω j))
      (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω)) z.2
      (fun i => ⟪z.1.val,z.2 i⟫) (fun t j i => taggedStep_congr t j _ (fun a => hz t a i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    rw [L.estimate_eq_taggedRoute,he] at hc
    exact hc
  apply (measure_mono_ae hmono).trans
  have hy (a : TaggedState M T) : (L.taggedOutput ω a).val =
      (match a with | .inl a => (L.output T ω a).val | .inr (t,a) => (L.output t ω a).val) := by
    cases a <;> rfl
  have hh := stopped_route_mixed_bound hτ (fun t j => (L.output t ω j).val) hε hε1 hb hab hq hqa
    (T := T) (taggedStart (L.initialChoice ω))
  have hset : S = {z : UnitSphere d × Samples d T | dist z.1.val
      (match streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
        (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
      | .inl a => (L.output T ω a).val | .inr (t,a) => (L.output t ω a).val) ≤ ε} := by
    ext z
    change (dist z.1.val (L.taggedOutput ω _).val ≤ ε) ↔ _
    rw [hy]
    rfl
  rw [hset]
  exact hh

end Learner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution.{u} : type_of% @_root_.OAI.NoiselessRegression.Learner.frozen_success_bound_local.{u} := @_root_.OAI.NoiselessRegression.Learner.frozen_success_bound_local.{u}
