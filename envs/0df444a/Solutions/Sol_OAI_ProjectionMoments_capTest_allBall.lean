-- Prove2me | solution 1 for OAI.ProjectionMoments.capTest_allBall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:00:16.918988+00:00
-- url     : https://prove2.me/submissions/d9e70b96-071f-4481-a5e5-f85cf97b7b8a

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapTests.lean:L127-L182
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.capTest_allBall. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_card_le_volume_ratio
import Theorems.Thm_OAI_NoiselessRegression_exists_net_of_finite_packing_bound
import Theorems.Thm_OAI_ProjectionMoments_sphere_cap_lower

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

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

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

end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rescale_preimage_closedBall (z b : E) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    rescale z R ⁻¹' Metric.closedBall b t = Metric.closedBall (dilate z R b) (R*t) := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have he : rescale z R x - b = R⁻¹ • (x - dilate z R b) := by
    simp [rescale, dilate, smul_sub, smul_add, smul_smul, hR.ne', sub_sub, add_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  rw [inv_mul_le_iff₀ hR]

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Caps ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_pos [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) ≠ 0 := by
  intro h
  have hh := sphere_cap_lower hc hr hr2
  rw [h,mul_zero] at hh
  exact (ENNReal.ofReal_pos.mpr (pow_pos hr _)).not_ge hh

end ProjectionMoments

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.CapTests ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_inv_bound [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ ≤
      ENNReal.ofReal ((r^(Module.finrank ℝ E-1))⁻¹ * (16:ℝ)^Module.finrank ℝ E) := by
  let p := NoiselessRegression.ambientSphereLaw (Metric.closedBall c r)
  let a := ENNReal.ofReal (r^(Module.finrank ℝ E-1))
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr _)).ne'
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have h := mul_le_mul' (le_rfl : a⁻¹ ≤ a⁻¹) (sphere_cap_lower hc hr hr2)
  change a⁻¹*a ≤ a⁻¹ * (ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) * p) at h
  rw [ENNReal.inv_mul_cancel ha0 hat, ← mul_assoc] at h
  have hh : p⁻¹ ≤ a⁻¹ * ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) := by
    apply (ENNReal.mul_le_mul_iff_right (cap_mass_pos hc hr hr2) (measure_ne_top _ _)).mp
    change p*p⁻¹ ≤ p*(a⁻¹ * ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E))
    rw [ENNReal.mul_inv_cancel (cap_mass_pos hc hr hr2) (measure_ne_top _ _)]
    simpa only [mul_comm] using h
  simpa only [a, ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.le _)),
    ENNReal.ofReal_inv_of_pos (pow_pos hr _)] using hh

lemma cap_ratio_algebra (d n : ℕ) {r ρ α : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hα : 2*α = n) :
    (r^n)⁻¹ * (16:ℝ)^d * (3*4^d*ρ^n) * (r/ρ)^α =
      3*64^d*(ρ/r)^α := by
  have hre : r^n = (r^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hr.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  have hρe : ρ^n = (ρ^α)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hρ.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    linarith
  rw [hre,hρe,Real.div_rpow hr.le hρ.le, Real.div_rpow hρ.le hr.le]
  have hc : (16:ℝ)^d * 4^d = 64^d := by rw [← mul_pow]; norm_num
  field_simp [(Real.rpow_pos_of_pos hr α).ne', (Real.rpow_pos_of_pos hρ α).ne']
  nlinarith [hc]

lemma cap_cost_ratio [Nontrivial E] {c c' : E} (hc : ‖c‖ = 1)
    {r ρ α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hρ : 0 < ρ)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) :
    (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c' ρ) * ENNReal.ofReal ((r/ρ)^α) ≤
        ENNReal.ofReal (3*64^Module.finrank ℝ E*(ρ/r)^α) := by
  have hu := NoiselessRegression.ambientSphereLaw_closedBall c' hρ (Module.finrank ℝ E-1) le_rfl
  have h := mul_le_mul' (mul_le_mul' (cap_mass_inv_bound hc hr hr2) hu)
    (le_rfl : ENNReal.ofReal ((r/ρ)^α) ≤ _)
  rw [← ENNReal.ofReal_mul (by positivity)] at hu
  apply le_trans (mul_le_mul' (mul_le_mul' (cap_mass_inv_bound hc hr hr2) hu) le_rfl)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    cap_ratio_algebra _ _ hr hρ hα]

lemma cap_small_scale_constant (d : ℕ) (hd : 1 ≤ d) {α ρ r t : ℝ}
    (hα0 : 0 ≤ α) (hαd : α ≤ d) (hr : 0 < r) (ht : 0 < t)
    (hρ : 0 ≤ ρ) (hρt : ρ ≤ 8*r*t) :
    3*64^d*(ρ/r)^α ≤ (2048:ℝ)^d*t^α := by
  have hratio : ρ/r ≤ 8*t := (div_le_iff₀ hr).mpr (by nlinarith)
  have h8 : (8:ℝ)^α ≤ (8:ℝ)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
  have h3 : (3:ℝ) ≤ 3^d := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd
  calc
    _ ≤ 3*64^d*(8*t)^α := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hρ hr.le) hratio hα0) (by positivity)
    _ = 3*64^d*8^α*t^α := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
    _ ≤ 3^d*64^d*8^d*t^α := by rw [Real.rpow_natCast] at h8; gcongr
    _ = (1536:ℝ)^d*t^α := by rw [← mul_pow, ← mul_pow]; norm_num
    _ ≤ _ := by gcongr; norm_num

lemma weighted_cap_set_le [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r b : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (h : E → ℝ≥0∞)
    (hb : ∫⁻ x, h x ∂capMeasure c r ≤ ENNReal.ofReal b) :
    (NoiselessRegression.ambientSphereLaw.withDensity h) (Metric.closedBall c r) ≤
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) * ENNReal.ofReal b := by
  rw [capMeasure, lintegral_smul_measure, smul_eq_mul] at hb
  rw [withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  exact (ENNReal.inv_mul_le_iff (cap_mass_pos hc hr hr2) (measure_ne_top _ _)).mp hb

lemma capTestMeasure_mass {h : E → ℝ≥0∞} {c : E} {r α : ℝ} (hr : 0 < r)
    (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    capTestMeasure h c r Set.univ ≤ 1 := by
  have hp := hdual D.parent
  rw [D.parent_center,D.parent_radius,div_self hr.ne',Real.one_rpow,ENNReal.ofReal_one] at hp
  simpa only [capTestMeasure,Measure.map_apply (measurable_rescale c r) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hp

lemma capTestMeasure_ball (h : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : 0 < r) (b : E) (t : ℝ) :
    capTestMeasure h c r (Metric.closedBall b t) =
      (NoiselessRegression.ambientSphereLaw (Metric.closedBall c r))⁻¹ *
        (NoiselessRegression.ambientSphereLaw.withDensity h)
          (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) := by
  rw [capTestMeasure, Measure.map_apply (measurable_rescale c r) Metric.isClosed_closedBall.measurableSet,
    rescale_preimage_closedBall c b hr, capMeasure, withDensity_smul_measure,
    Measure.smul_apply, smul_eq_mul, ← restrict_withDensity Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]

lemma capTest_allBall [Nontrivial E] {h : E → ℝ≥0∞} {c : E} (hc : ‖c‖ = 1)
    {r α : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (hα0 : 0 ≤ α)
    (hα : 2*α = (Module.finrank ℝ E-1:ℕ)) (D : CapDictionary c r α)
    (hdual : ∀ i, ∫⁻ x, h x ∂capMeasure (D.center i) (D.radius i) ≤ ENNReal.ofReal ((r/D.radius i)^α)) :
    AllBallMass (capTestMeasure h c r) ((2048:ℝ)^Module.finrank ℝ E) α := by
  have hd : 1 ≤ Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  have hαd : α ≤ Module.finrank ℝ E := by
    have hn : ((Module.finrank ℝ E-1:ℕ):ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
    linarith
  intro b t ht
  by_cases ht4 : t ≤ 1/4
  · let ξ := NoiselessRegression.ambientSphereLaw.withDensity h
    let T := (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) ∩ Metric.sphere 0 1
    have he : ξ (Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r) = ξ T := by
      apply measure_congr
      filter_upwards [(withDensity_absolutelyContinuous NoiselessRegression.ambientSphereLaw h).ae_le
        (NoiselessRegression.ambientSphereLaw_ae_norm (E := E))] with x hx
      have hs : x ∈ Metric.sphere (0:E) 1 := by simpa using hx
      apply propext
      change x ∈ Metric.closedBall (dilate c r b) (r*t) ∩ Metric.closedBall c r ↔ x ∈ T
      simp only [T, Set.mem_inter_iff, hs, and_true]
    rw [capTestMeasure_ball h c hr, he]
    by_cases hT : T.Nonempty
    · obtain ⟨s,hs⟩ := hT
      have hsn : ‖s‖ = 1 := by simpa using hs.2
      obtain ⟨i,hi1,hi2,hsi⟩ := D.cover s hsn t ht ht4
      have hsub : T ⊆ Metric.closedBall (D.center i) (D.radius i) := by
        intro x hx
        change dist x (D.center i) ≤ D.radius i
        have hxB : dist x (dilate c r b) ≤ r*t := hx.1.1
        have hsB : dist s (dilate c r b) ≤ r*t := hs.1.1
        calc
          _ ≤ dist x s + dist s (D.center i) := dist_triangle _ _ _
          _ ≤ (dist x (dilate c r b) + dist (dilate c r b) s) + D.radius i/2 :=
            add_le_add (dist_triangle _ _ _) hsi
          _ ≤ D.radius i := by rw [dist_comm (dilate c r b) s]; linarith
      apply (mul_le_mul' le_rfl (measure_mono hsub)).trans
      have htest := weighted_cap_set_le (D.center_norm i) (D.radius_pos i)
        ((D.radius_le i).trans hr2) h (hdual i)
      apply (mul_le_mul' le_rfl htest).trans
      rw [← mul_assoc]
      exact (cap_cost_ratio hc hr hr2 (D.radius_pos i) hα).trans
        (ENNReal.ofReal_le_ofReal (cap_small_scale_constant _ hd hα0 hαd hr ht (D.radius_pos i).le hi2.le))
    · rw [Set.not_nonempty_iff_eq_empty.mp hT, measure_empty, mul_zero]
      exact bot_le
  · apply (measure_mono (Set.subset_univ _)).trans ((capTestMeasure_mass hr D hdual).trans ?_)
    have h4t : 1 ≤ 4*t := by linarith
    have hpow : 1 ≤ (4*t)^α := Real.one_le_rpow h4t hα0
    have h4 : (4:ℝ)^α ≤ (2048:ℝ)^Module.finrank ℝ E := by
      calc
        _ ≤ (4:ℝ)^(Module.finrank ℝ E:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hαd
        _ = (4:ℝ)^Module.finrank ℝ E := Real.rpow_natCast _ _
        _ ≤ _ := by gcongr; norm_num
    rw [Real.mul_rpow (by norm_num) ht.le] at hpow
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hpow.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht.le α)))

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.capTest_allBall := @_root_.OAI.ProjectionMoments.capTest_allBall
