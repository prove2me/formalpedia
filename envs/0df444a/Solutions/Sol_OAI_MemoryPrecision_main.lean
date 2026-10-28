-- Prove2me | solution 1 for OAI.MemoryPrecision.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T21:18:10.329982+00:00
-- url     : https://prove2.me/submissions/3b69d0a0-cabf-4e1d-a66a-a51a95432903

import Mathlib
import Definitions.Def_MemoryPrecision
import Definitions.Def_OAIQ1Mp000
import Theorems.Thm_OAI_MemoryPrecision_Kernel_source_cube_success

section
-- module Solutions.OAIQ1_Mem.Compat
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_InverseMoments
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Nets
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_AffineTubes
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Sphere
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_GaussianKernel
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_ReplicaMoments
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

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

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Smoothing
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Projection
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Stream
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end StreamAux

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Caps
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end StreamCaps

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Observation
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

lemma projectionLaw_absolutelyContinuous {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (hn : 1 ≤ n) (hmargin : n+m ≤ a) :
    projectionLaw ν m ≪ matrixLabelReference (E := E) m := by
  let ν' := C⁻¹ • ν
  have hCi : C⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hC
  let : IsFiniteMeasure ν' := ⟨by simp only [ν', Measure.smul_apply, smul_eq_mul]; finiteness⟩
  have hlocal : HasLocalMassBound ν' (a : ℝ) := by
    intro z _ r hr
    have hh := mul_le_mul' (le_rfl : C⁻¹ ≤ C⁻¹) (hν z r hr)
    simpa only [ν', Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hC hCt, one_mul, Real.rpow_natCast] using hh
  have hs : ν'.support ⊆ Metric.closedBall 0 1 :=
    (Measure.smul_absolutelyContinuous.support_mono).trans hsupport
  have hbound (S : Set ((Fin m → E) × (Fin m → ℝ))) :=
    projectionLaw_set_bound hlocal hs m n hn (by exact_mod_cast hmargin) S
  have he : projectionLaw ν' m = C⁻¹ • projectionLaw ν m := by
    simp only [projectionLaw, ν', Measure.prod_smul_right]
    exact Measure.map_smul _ _ _
  intro S hS
  have h := hbound S
  rw [hS, ENNReal.zero_rpow_of_pos (by
    have : (1 : ℝ) < n+1 := by exact_mod_cast (by omega : 1 < n+1)
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr this)), mul_zero, he,
    Measure.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (le_antisymm h bot_le)).resolve_left (ENNReal.inv_ne_zero.mpr hCt)

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
end

section
-- module Solutions.OAIQ1_Mem.GaussianRegression_Transfer
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

end StreamTransfer

end NoiselessRegression

end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_AmbientGram
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v



open MeasureTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma specialized_gram_product_bound (d m p : ℕ) (hd : 16 ≤ d) (hp : p=d/8)
    (hm : 1 ≤ m) (hmp : m ≤ p) (β : ℝ)
    (hβlo : ((d:ℝ)-1)/2 ≤ β) (hβhi : β ≤ (d:ℝ)/2)
    (H R : ℝ) (hH : 0 < H) (hR : 0 < R) :
    H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (∏ j : Fin (p-1), J β m j) ≤
      (7:ℝ)^(d*(p-1)) * H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) := by
  have hp2 : 2 ≤ p := by omega
  have hs := specialized_J_bound d m p hd hp hm hmp β hβlo hβhi
  have hprod : (∏ j : Fin (p-1), J β m j) ≤ (7:ℝ)^(d*(p-1)) := by
    calc
      _ ≤ ∏ _j : Fin (p-1), (7:ℝ)^d := by
        apply Finset.prod_le_prod
        · intro j _
          apply (J_pos ?_).le
          have hh := hs j (by have := j.isLt; omega)
          have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
          linarith [hh.1, hh.2.1]
        · intro j _
          exact (hs j (by have := j.isLt; omega)).2.2
      _ = _ := by simp [← pow_mul]
  calc
    _ ≤ H^p * R^(β*(p:ℝ)-(m:ℝ)*(p-1:ℕ)) * (7:ℝ)^(d*(p-1)) := by gcongr
    _ = _ := by ring

theorem ambient_gram : AmbientGramStatement := by
  constructor
  · intro d m p _hd hm hp β R H hβ hR hH μ hfin z hsupport hball
    let : IsFiniteMeasure μ := hfin
    have hm0 : 0 < m := by omega
    have hp1 : 1 ≤ p := by omega
    have hgap : ((p-1:ℕ):ℝ)+(m:ℝ)-1<β := by
      rw [Nat.cast_sub hp1]
      push_cast
      linarith
    refine ⟨?_, ?_, ?_⟩
    · intro j hj L hnonempty hdim
      let : Nonempty L := hnonempty
      have hj' : (j:ℝ)+2 ≤ p := by exact_mod_cast (show j+2 ≤ p by omega)
      constructor
      · intro t ht htR
        simpa only [hdim] using ambient_tube hR hsupport hball L ht htR
      · have hi := (ambient_inverse_moment hH hR hsupport hball L hm0
          (by rw [hdim]; linarith)).2
        simpa only [hdim] using hi
    · exact ae_joint_replica_independent hH hR hsupport hball hm0 (p-1) hgap
    · have hi := joint_replica_integral_exact hH hR hsupport hball hm0 (p-1) hgap
      simpa only [NoiselessRegression.replicaWeight_eq_det, InverseGram,
        Nat.sub_add_cancel hp1] using hi
  · refine ⟨7, by norm_num, ?_⟩
    intro d m p hd hp hm hmp β hβlo hβhi
    exact ⟨specialized_J_bound d m p hd hp hm hmp β hβlo hβhi,
      specialized_gram_product_bound d m p hd hp hm hmp β hβlo hβhi⟩

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_FiniteDensity
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

theorem finite_density : FiniteDensityStatement := by
  intro d m p _ hm hp β H R hgap hH hR z μ hμ hs hb
  let := hμ
  exact exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_MeasurableTests
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

section TestTransfer
variable {X : Type*} [mX : MeasurableSpace X]

lemma trim_completion (ν : Measure X) :
    ν.completion.trim (original_le_completion ν) = ν := by
  unfold NullMeasurableSpace at *
  apply Measure.ext
  intro S hS
  exact trim_measurableSet_eq (original_le_completion ν) hS

lemma lintegral_completion (ν : Measure X) {f : X → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ x, f x ∂ν.completion) = ∫⁻ x, f x ∂ν := by
  have ht : @Measure.trim X mX (inferInstance : MeasurableSpace (NullMeasurableSpace X ν))
      ν.completion (original_le_completion ν) = ν := trim_completion ν
  have h := lintegral_trim_ae (α := X) (μ := ν.completion) (original_le_completion ν)
    (f := f) (by rwa [ht])
  rw [ht] at h
  exact h.symm

lemma eLpNorm_completion (ν : Measure X) (F : X → ℝ) (hF : Measurable F) (p : ℕ)
    (hp : p ≠ 0) : eLpNorm F (p:ℝ≥0∞) ν.completion = eLpNorm F (p:ℝ≥0∞) ν := by
  have hFc : @Measurable (NullMeasurableSpace X ν) ℝ _ _ F :=
    hF.mono (original_le_completion ν) le_rfl
  erw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by finiteness),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp) (by finiteness),
    lintegral_completion ν (by fun_prop)]

lemma density_set_bound (ν : Measure X) (F : X → ℝ) (hF : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) (p : ℕ) (hp : 2 ≤ p) (B : ℝ≥0∞)
    (hnorm : eLpNorm F (p:ℝ≥0∞) ν ≤ B) (E : Set X) (hE : MeasurableSet E) :
    ν.withDensity (fun x => ENNReal.ofReal (F x)) E ≤ B * (ν E)^(1-1/(p:ℝ)) := by
  have h := density_test_bound ν F hF hF0 p hp B hnorm Set.univ MeasurableSet.univ
    (by simp) (E.indicator 1) (measurable_one.indicator hE).aemeasurable
    (fun x => (Set.indicator_le (g := fun _ => (1:ℝ≥0∞)) (fun _ _ => le_rfl)) x)
  simpa only [lintegral_indicator hE, Measure.restrict_apply_univ,
    setLIntegral_const, Pi.one_apply, one_mul, Measure.restrict_univ] using h

lemma withDensity_completion_apply (ν : Measure X) (F : X → ℝ) (hF : Measurable F)
    (E : Set X) (hE : NullMeasurableSet E ν) :
    ν.completion.withDensity (fun x => ENNReal.ofReal (F x)) E =
      ν.withDensity (fun x => ENNReal.ofReal (F x)) E := by
  erw [withDensity_apply _ hE, withDensity_apply₀ _ hE,
    ← lintegral_indicator hE, ← lintegral_indicator₀ hE,
    lintegral_completion ν (hF.ennreal_ofReal.aemeasurable.indicator₀ hE)]
end TestTransfer

theorem measurable_test : MeasurableTestStatement := by
  intro d m p hd hm hp β H R hgap hH hR z μ hμ hs hb
  let := hμ
  obtain ⟨F, hF, hF0, hden, hsupp, hnorm⟩ :=
    exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
  dsimp only
  let ν := MatrixLabelReference d m
  let B := ENNReal.ofReal (ProjectionNormScale m p H β R)
  refine ⟨?_, ?_, ?_⟩
  · intro E hE _
    rw [← hden]
    exact density_set_bound ν F hF hF0 p hp B hnorm E hE
  · rw [← hden]
    exact withDensity_absolutelyContinuous _ _
  · let ηc := ν.completion.withDensity (fun x => ENNReal.ofReal (F x))
    refine ⟨ηc, ?_, ?_, ?_⟩
    · intro E hE
      calc
        ηc E = ν.withDensity (fun x => ENNReal.ofReal (F x)) E :=
          withDensity_completion_apply ν F hF E hE
        _ = ProjectionLaw μ m E := congrArg (fun q => q E) hden
    · intro E hE _
      have hFc : @Measurable (NullMeasurableSpace _ ν) ℝ _ _ F :=
        hF.mono (original_le_completion ν) le_rfl
      have hnormc : eLpNorm F (p:ℝ≥0∞) ν.completion ≤ B := by
        erw [eLpNorm_completion ν F hF p (by omega)]
        exact hnorm
      exact density_set_bound ν.completion F hFc hF0 p hp B hnormc E hE
    · intro φ hφ hφ1
      have hFc : @Measurable (NullMeasurableSpace _ ν) ℝ _ _ F :=
        hF.mono (original_le_completion ν) le_rfl
      have hnormc : eLpNorm F (p:ℝ≥0∞) ν.completion ≤ B := by
        erw [eLpNorm_completion ν F hF p (by omega)]
        exact hnorm
      exact density_test_bound ν.completion F hFc hF0 p hp B hnormc
        (ProjectedEllipsoid z R) (isClosed_projectedEllipsoid z R).measurableSet.nullMeasurableSet
        hsupp φ hφ.aemeasurable hφ1
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_RealContinuation
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma blockCount_mul_ge (T : ℕ) {p : ℕ} (hp : 0 < p) : T ≤ BlockCount T p * p := by
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have h := (div_le_iff₀ hp').mp (Nat.le_ceil ((T:ℝ)/(p:ℝ)))
  exact_mod_cast h
lemma blockCount_pos {T p : ℕ} (hT : 0 < T) (hp : 0 < p) : 0 < BlockCount T p := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hT) (by exact_mod_cast hp)

lemma stepConstant_one : 1 ≤ StepConstant := (Classical.choose_spec coefficient_step).1
lemma stepConstant_pos : 0 < StepConstant := lt_of_lt_of_le zero_lt_one stepConstant_one

lemma realStep_one (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ RealStep d N := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ stepConstant_one
  · exact Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
lemma realStep_pos (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 0 < RealStep d N :=
  lt_of_lt_of_le zero_lt_one (realStep_one d hN)

lemma SphereBallBound.mono {d : ℕ} {h : Sphere d → ℝ≥0∞} {H K α : ℝ}
    (hh : SphereBallBound h H α) (hHK : H ≤ K) : SphereBallBound h K α := by
  intro z r hr
  exact (hh z r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hHK (by positivity)))

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_RadialMixture
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma coordinateUnit_norm (m : ℕ) (hm : 1 ≤ m) : ‖CoordinateUnit m‖ = 1 := by
  have he : ‖CoordinateUnit m‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin m, (if (j:ℕ) = 0 then (1:ℝ) else 0)^2) = 1
    let j : Fin m := ⟨0, by omega⟩
    rw [Finset.sum_eq_single j]
    · simp [j]
    · intro b _ hb
      have hb0 : (b:ℕ) ≠ 0 := by intro h; apply hb; exact Fin.ext h
      simp [hb0]
    · simp
  nlinarith [norm_nonneg (CoordinateUnit m)]

lemma gaussianKernel_radial (m : ℕ) (δ : ℝ) (y : Space m) :
    GaussianKernel m δ y = GaussianAmplitude m δ *
      Real.exp (-‖y‖^2 / (2*δ^2)) := by
  change (∏ j, (Real.sqrt (2*Real.pi*δ^2))⁻¹ *
    Real.exp (-(y j - 0)^2 / (2*δ^2))) = _
  simp only [sub_zero, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← Real.exp_sum]
  unfold GaussianAmplitude
  simp only [one_div, Fintype.card_fin]
  congr 1
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_div, Finset.sum_neg_distrib]

lemma gaussianKernel_nonneg (m : ℕ) (δ : ℝ) (y : Space m) :
    0 ≤ GaussianKernel m δ y :=
  Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)

lemma gaussianKernel_continuous (m : ℕ) (δ : ℝ) : Continuous (GaussianKernel m δ) := by
  have he : GaussianKernel m δ = fun y => GaussianAmplitude m δ *
      Real.exp (-‖y‖^2 / (2*δ^2)) := funext (gaussianKernel_radial m δ)
  rw [he]
  fun_prop

lemma unitBallVolume_pos (m : ℕ) : 0 < UnitBallVolume m := by
  exact ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

lemma volume_ball_eq (m : ℕ) (hm : 1 ≤ m) (x : Space m) {r : ℝ} (hr : 0 < r) :
    (volume : Measure (Space m)) (Metric.ball x r) =
      ENNReal.ofReal (UnitBallVolume m * r^m) := by
  have : NeZero m := ⟨by omega⟩
  rw [Measure.addHaar_ball volume x hr.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (unitBallVolume_pos m).le, mul_comm,
    UnitBallVolume, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  rfl

lemma gaussianKernel_radial_line (m : ℕ) (hm : 1 ≤ m) (δ r : ℝ) :
    GaussianKernel m δ (r • CoordinateUnit m) =
      GaussianAmplitude m δ * Real.exp (-r^2/(2*δ^2)) := by
  rw [gaussianKernel_radial, norm_smul, coordinateUnit_norm m hm, mul_one,
    Real.norm_eq_abs, sq_abs]

lemma gaussianRadial_deriv (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -GaussianKernel m δ (r • CoordinateUnit m))
      ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) r := by
  simp_rw [gaussianKernel_radial_line m hm]
  have ht := ((((hasDerivAt_id r).pow 2).neg.div_const (2*δ^2)).exp.const_mul
    (GaussianAmplitude m δ)).neg
  convert! ht using 1
  simp [id]
  field_simp

lemma gaussianRadial_tendsto (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun r : ℝ => -GaussianKernel m δ (r • CoordinateUnit m)) atTop (𝓝 0) := by
  simp_rw [gaussianKernel_radial_line m hm]
  have he : Tendsto (fun r : ℝ => -r^2/(2*δ^2)) atTop atBot := by
    have hsq : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
    exact Filter.Tendsto.atBot_div_const (by positivity) (tendsto_neg_atTop_atBot.comp hsq)
  have ht := (Real.tendsto_exp_atBot.comp he).const_mul (GaussianAmplitude m δ)
  simpa using ht.neg

lemma gaussianRadial_tail (m : ℕ) (hm : 1 ≤ m) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    (∫ r in Set.Ioi ρ, (r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) =
      GaussianKernel m δ (ρ • CoordinateUnit m) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_ : r ∈ Set.Ici ρ) => gaussianRadial_deriv m hm hδ r)
    (fun _ hr => mul_nonneg (div_nonneg (le_trans hρ hr.le) (sq_nonneg δ))
      (gaussianKernel_nonneg m δ _)) (gaussianRadial_tendsto m hm hδ)
  simpa using h

lemma gaussianKernel_integral (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : Space m, GaussianKernel m δ y) = 1 := by
  rw [← (PiLp.volume_preserving_toLp (Fin m)).integral_comp
    (show MeasurableEmbedding (WithLp.toLp 2 : (Fin m → ℝ) → Space m) from
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding)]
  change (∫ y : Fin m → ℝ, ∏ j, gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j)) = 1
  rw [integral_fintype_prod_volume_eq_pow, integral_gaussianPDFReal_eq_one 0
    (show (⟨δ^2,sq_nonneg δ⟩ : ℝ≥0) ≠ 0 from by
      intro h; have := congrArg (fun x : ℝ≥0 => (x:ℝ)) h; change δ^2 = 0 at this; nlinarith)]
  simp

lemma gaussianKernel_lintegral (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ y : Space m, ENNReal.ofReal (GaussianKernel m δ y)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_of_integral_eq_one (gaussianKernel_integral m hδ))
    (Eventually.of_forall (gaussianKernel_nonneg m δ)), gaussianKernel_integral m hδ]
  simp

lemma gaussianRadial_integrable (m : ℕ) (hm : 1 ≤ m) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    IntegrableOn (fun r : ℝ => (r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) (Ioi ρ) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun r (_ : r ∈ Set.Ici ρ) => gaussianRadial_deriv m hm hδ r)
    (fun _ hr => mul_nonneg (div_nonneg (le_trans hρ hr.le) (sq_nonneg δ))
      (gaussianKernel_nonneg m δ _)) (gaussianRadial_tendsto m hm hδ)

lemma gaussianRadial_ltail (m : ℕ) (hm : 1 ≤ m) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    (∫⁻ r in Ioi ρ, ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) =
      ENNReal.ofReal (GaussianKernel m δ (ρ • CoordinateUnit m)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianRadial_integrable m hm hδ hρ)
    ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr =>
      mul_nonneg (div_nonneg (le_trans hρ hr.le) (sq_nonneg δ)) (gaussianKernel_nonneg m δ _))),
    gaussianRadial_tail m hm hδ hρ]

lemma gaussianKernel_ball_mixture (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (y : Space m) :
    ENNReal.ofReal (GaussianKernel m δ y) =
      ∫⁻ r in Ioi 0, (Metric.ball (0 : Space m) r).indicator
        (fun _ => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) y := by
  have he (r : ℝ) : (Metric.ball (0 : Space m) r).indicator
        (fun _ => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) y =
      (Ioi ‖y‖).indicator
        (fun r => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) r := by
    have hb : y ∈ Metric.ball (0 : Space m) r ↔ ‖y‖ < r := by simp
    by_cases h : ‖y‖ < r
    · rw [Set.indicator_of_mem (hb.mpr h), Set.indicator_of_mem (show r ∈ Ioi ‖y‖ from h)]
    · rw [Set.indicator_of_notMem (mt hb.mp h), Set.indicator_of_notMem (show r ∉ Ioi ‖y‖ from h)]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (norm_nonneg y)), gaussianRadial_ltail m hm hδ (norm_nonneg y),
    gaussianKernel_radial_line m hm, gaussianKernel_radial]

lemma radialMixture_nonneg (m : ℕ) (δ : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ RadialMixture m δ r := by
  unfold RadialMixture
  exact mul_nonneg (mul_nonneg (mul_nonneg (unitBallVolume_pos m).le (pow_nonneg hr.le _))
    (div_nonneg hr.le (sq_nonneg δ))) (gaussianKernel_nonneg m δ _)

lemma radialMixture_measurable (m : ℕ) (δ : ℝ) : Measurable (RadialMixture m δ) := by
  unfold RadialMixture
  exact (continuous_const.mul (continuous_id.pow _ ) |>.mul
    (continuous_id.div_const _) |>.mul
      ((gaussianKernel_continuous m δ).comp (continuous_id.smul continuous_const))).measurable

lemma radialMixture_lintegral (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ r in Ioi 0, ENNReal.ofReal (RadialMixture m δ r)) = 1 := by
  have hmeas : Measurable (fun z : Space m × ℝ =>
      (Metric.ball (0 : Space m) z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) := by
    have he : (fun z : Space m × ℝ => (Metric.ball (0 : Space m) z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) =
      {z : Space m × ℝ | ‖z.1‖ < z.2}.indicator
        (fun z => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) := by
      ext z
      by_cases hz : ‖z.1‖ < z.2
      · rw [Set.indicator_of_mem (show z.1 ∈ Metric.ball (0 : Space m) z.2 by simpa using hz),
          Set.indicator_of_mem (show z ∈ {z : Space m × ℝ | ‖z.1‖ < z.2} from hz)]
      · rw [Set.indicator_of_notMem (show z.1 ∉ Metric.ball (0 : Space m) z.2 by simpa using hz),
          Set.indicator_of_notMem (show z ∉ {z : Space m × ℝ | ‖z.1‖ < z.2} from hz)]
    rw [he]
    have hk : Measurable (GaussianKernel m δ) := (gaussianKernel_continuous m δ).measurable
    exact (by fun_prop : Measurable (fun z : Space m × ℝ =>
      ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m)))).indicator
      (measurableSet_lt (by fun_prop) (by fun_prop))
  have he := gaussianKernel_lintegral m hδ
  simp_rw [gaussianKernel_ball_mixture m hm hδ] at he
  rw [lintegral_lintegral_swap hmeas.aemeasurable] at he
  convert he using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const,
    volume_ball_eq m hm 0 hr]
  unfold RadialMixture
  rw [← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hr.le (sq_nonneg δ))
    (gaussianKernel_nonneg m δ _))]
  congr 1
  ring

lemma radialMixture_integral (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) :
    (∫ r in Ioi 0, RadialMixture m δ r) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr => radialMixture_nonneg m δ hr))
    (radialMixture_measurable m δ).aestronglyMeasurable, radialMixture_lintegral m hm hδ]
  simp

lemma radialMixture_tail (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianKernel m δ y =
      ∫ r in Ioi ‖y‖, RadialMixture m δ r / (UnitBallVolume m * r^m) := by
  rw [integral_congr_ae (show (fun r => RadialMixture m δ r / (UnitBallVolume m * r^m)) =ᵐ[
    volume.restrict (Ioi ‖y‖)] (fun r => (r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg y) hr
      unfold RadialMixture
      field_simp [(unitBallVolume_pos m).ne', hr0.ne']), gaussianRadial_tail m hm hδ (norm_nonneg y),
    gaussianKernel_radial_line m hm, gaussianKernel_radial]
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_BallAverages
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma gaussianKernel_scale (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianKernel m δ (δ • y) = δ⁻¹ ^ m * GaussianKernel m 1 y := by
  have he (a : ℝ) : gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (δ*a) =
      δ⁻¹ * gaussianPDFReal 0 1 a := by
    have h := gaussianPDFReal_inv_mul (μ := 0) (v := 1) hδ.ne' (δ*a)
    simp only [inv_mul_cancel_left₀ hδ.ne', mul_zero, mul_one, abs_of_pos hδ] at h
    rw [h]
    field_simp
    rfl
  unfold GaussianKernel
  simp only [PiLp.smul_apply, smul_eq_mul, one_pow]
  simp_rw [he]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

lemma radialMixture_scale (m : ℕ) {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    RadialMixture m δ (δ*r) = δ⁻¹ * RadialMixture m 1 r := by
  unfold RadialMixture
  rw [mul_smul, gaussianKernel_scale m hδ]
  simp only [one_pow, div_one, mul_pow, inv_pow]
  field_simp

lemma ballAverage_measurable {m : ℕ} (ν : Measure (Space m)) (y : Space m) :
    Measurable (BallAverage ν y) := by
  have h : Monotone (fun r : ℝ => ν (Metric.ball y r)) := fun r t h =>
    measure_mono (Metric.ball_subset_ball h)
  exact h.measurable.ennreal_toReal.div (by fun_prop)

lemma ballAverage_nonneg {m : ℕ} (ν : Measure (Space m)) (y : Space m) {r : ℝ}
    (hr : 0 < r) : 0 ≤ BallAverage ν y r := by
  exact div_nonneg ENNReal.toReal_nonneg (mul_nonneg (unitBallVolume_pos m).le
    (pow_nonneg hr.le _))

lemma ac_ball_eq_closedBall {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    (hν : ν ≪ volume) (y : Space m) (r : ℝ) :
    ν (Metric.ball y r) = ν (Metric.closedBall y r) := by
  have : NeZero m := ⟨by omega⟩
  apply measure_eq_measure_of_null_sdiff Metric.ball_subset_closedBall
  rw [Metric.closedBall_sdiff_ball]
  exact hν (Measure.addHaar_sphere volume y r)

lemma ae_tendsto_ballAverage {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ∀ᵐ y ∂(volume : Measure (Space m)), Tendsto (BallAverage ν y)
      (𝓝[>] (0:ℝ)) (𝓝 ((ν.rnDeriv volume y).toReal)) := by
  have : NeZero m := ⟨by omega⟩
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν volume, ν.rnDeriv_lt_top volume] with y hy hyfin
  have ht := (ENNReal.continuousAt_toReal hyfin.ne).tendsto.comp hy
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  unfold BallAverage
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_div, Measure.addHaar_closedBall_eq_addHaar_ball volume y r,
    ← ac_ball_eq_closedBall hm ν hν y r, volume_ball_eq m hm y hr,
    ENNReal.toReal_ofReal (mul_nonneg (unitBallVolume_pos m).le (pow_nonneg hr.le _))]

lemma ballAverage_bounded {m : ℕ} (ν : Measure (Space m)) [IsFiniteMeasure ν]
    (y : Space m) {f : ℝ} (hf : 0 ≤ f)
    (ht : Tendsto (BallAverage ν y) (𝓝[>] (0:ℝ)) (𝓝 f)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ‖BallAverage ν y r‖ ≤ B := by
  rcases Metric.tendsto_nhdsWithin_nhds.mp ht 1 zero_lt_one with ⟨b,hb,hnear⟩
  let C : ℝ := max (f+1) ((ν Set.univ).toReal / (UnitBallVolume m * b^m))
  refine ⟨C, le_trans (by linarith : 0 ≤ f+1) (le_max_left _ _), ?_⟩
  intro r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (ballAverage_nonneg ν y hr)]
  by_cases h : r < b
  · have he := hnear hr (by simpa [Real.dist_eq, abs_of_pos hr] using h)
    have he' : BallAverage ν y r < f+1 := by
      rw [Real.dist_eq] at he
      have := (abs_lt.mp he).2
      linarith
    exact he'.le.trans (le_max_left _ _)
  · apply le_trans ?_ (le_max_right _ _)
    unfold BallAverage
    have hvol : 0 < UnitBallVolume m := unitBallVolume_pos m
    apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
        (measure_mono (Set.subset_univ _))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb.le (le_of_not_gt h) _)
        (unitBallVolume_pos m).le

lemma tendsto_radial_average {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m)) [IsFiniteMeasure ν]
    (y : Space m) {f : ℝ} (hf : 0 ≤ f)
    (ht : Tendsto (BallAverage ν y) (𝓝[>] (0:ℝ)) (𝓝 f)) :
    Tendsto (fun δ : ℝ => ∫ r in Ioi 0, RadialMixture m 1 r * BallAverage ν y (δ*r))
      (𝓝[>] (0:ℝ)) (𝓝 f) := by
  obtain ⟨B,hB,hbound⟩ := ballAverage_bounded ν y hf ht
  have hw : IntegrableOn (RadialMixture m 1) (Ioi 0) :=
    integrable_of_integral_eq_one (radialMixture_integral m hm zero_lt_one)
  have hl := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (l := 𝓝[>] (0:ℝ))
    (F := fun δ r => RadialMixture m 1 r * BallAverage ν y (δ*r))
    (f := fun r => RadialMixture m 1 r * f)
    (fun r => RadialMixture m 1 r * B)
    (Eventually.of_forall (fun δ =>
      ((radialMixture_measurable m 1).mul ((ballAverage_measurable ν y).comp
        (by fun_prop))).aestronglyMeasurable))
    (show ∀ᶠ δ in 𝓝[>] (0:ℝ), ∀ᵐ r ∂volume.restrict (Ioi 0),
      ‖RadialMixture m 1 r * BallAverage ν y (δ*r)‖ ≤ RadialMixture m 1 r * B from by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (radialMixture_nonneg m 1 hr)]
      exact mul_le_mul_of_nonneg_left (hbound _ (mul_pos hδ hr)) (radialMixture_nonneg m 1 hr))
    (hw.mul_const B) (show ∀ᵐ r ∂volume.restrict (Ioi 0),
      Tendsto (fun δ => RadialMixture m 1 r * BallAverage ν y (δ*r))
        (𝓝[>] (0:ℝ)) (𝓝 (RadialMixture m 1 r * f)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      apply Tendsto.const_mul
      apply ht.comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa using ((continuous_id.mul_const r).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        change 0 < δ*r
        exact mul_pos hδ hr)
  simpa only [integral_mul_const, radialMixture_integral m hm zero_lt_one, one_mul] using hl
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_GaussianConvolution
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma gaussianKernel_translated_ball_mixture (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (y x : Space m) :
    ENNReal.ofReal (GaussianKernel m δ (y-x)) =
      ∫⁻ r in Ioi 0, (Metric.ball y r).indicator
        (fun _ => ENNReal.ofReal ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m))) x := by
  rw [gaussianKernel_ball_mixture m hm hδ]
  apply lintegral_congr
  intro r
  have he : y-x ∈ Metric.ball (0 : Space m) r ↔ x ∈ Metric.ball y r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hx : x ∈ Metric.ball y r
  · rw [Set.indicator_of_mem (he.mpr hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (mt he.mp hx), Set.indicator_of_notMem hx]

lemma gaussianConvolution_shell {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianConvolution ν δ y = ∫ r in Ioi 0,
      ((r/δ^2)*GaussianKernel m δ (r • CoordinateUnit m)) * (ν (Metric.ball y r)).toReal := by
  have hk : Measurable (GaussianKernel m δ) := (gaussianKernel_continuous m δ).measurable
  have hmeas : Measurable (fun z : Space m × ℝ =>
      (Metric.ball y z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) := by
    have he : (fun z : Space m × ℝ => (Metric.ball y z.2).indicator
        (fun _ => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) z.1) =
      {z : Space m × ℝ | dist z.1 y < z.2}.indicator
        (fun z => ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m))) := by
      ext z
      by_cases hz : z.1 ∈ Metric.ball y z.2
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem
          (show z ∈ {z : Space m × ℝ | dist z.1 y < z.2} from hz)]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem
          (show z ∉ {z : Space m × ℝ | dist z.1 y < z.2} from hz)]
    rw [he]
    exact (by fun_prop : Measurable (fun z : Space m × ℝ =>
      ENNReal.ofReal ((z.2/δ^2)*GaussianKernel m δ (z.2 • CoordinateUnit m)))).indicator
      (measurableSet_lt (by fun_prop) (by fun_prop))
  unfold GaussianConvolution
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => gaussianKernel_nonneg m δ _))
    ((hk.comp (by fun_prop)).aestronglyMeasurable)]
  simp_rw [gaussianKernel_translated_ball_mixture m hm hδ y]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  simp_rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  have hmass : Measurable (fun r : ℝ => (ν (Metric.ball y r)).toReal) :=
    (show Monotone (fun r : ℝ => ν (Metric.ball y r)) from
      fun a b h => measure_mono (Metric.ball_subset_ball h)).measurable.ennreal_toReal
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr =>
      mul_nonneg (mul_nonneg (div_nonneg hr.le (sq_nonneg δ)) (gaussianKernel_nonneg m δ _))
        ENNReal.toReal_nonneg)) (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [ENNReal.ofReal_mul (mul_nonneg (div_nonneg hr.le (sq_nonneg δ))
    (gaussianKernel_nonneg m δ _)), ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma gaussianConvolution_mixture {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianConvolution ν δ y = ∫ r in Ioi 0, RadialMixture m δ r * BallAverage ν y r := by
  rw [gaussianConvolution_shell hm ν hδ y]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  unfold RadialMixture BallAverage
  field_simp [(unitBallVolume_pos m).ne', hr0.ne']

lemma gaussianConvolution_scaled_mixture {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) (y : Space m) :
    GaussianConvolution ν δ y = ∫ r in Ioi 0, RadialMixture m 1 r * BallAverage ν y (δ*r) := by
  rw [gaussianConvolution_mixture hm ν hδ y]
  have he := integral_comp_mul_left_Ioi'
    (fun r => RadialMixture m δ r * BallAverage ν y r) 0 hδ
  simp only [mul_zero, smul_eq_mul] at he
  rw [← he, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun radius => by
    dsimp only
    rw [radialMixture_scale m hδ]
    field_simp [hδ.ne'])

lemma ae_tendsto_gaussianConvolution {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Space m))
    [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ∀ᵐ y ∂(volume : Measure (Space m)), Tendsto (fun δ : ℝ => GaussianConvolution ν δ y)
      (𝓝[>] (0:ℝ)) (𝓝 ((ν.rnDeriv volume y).toReal)) := by
  filter_upwards [ae_tendsto_ballAverage hm ν hν] with y hy
  apply (tendsto_radial_average hm ν y ENNReal.toReal_nonneg hy).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (gaussianConvolution_scaled_mixture hm ν hδ y).symm
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_LabelTranslations
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
section Translation
variable {Ω Y : Type*}
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [R1Space Ω]
  [NormedAddCommGroup Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (γ : Measure Ω) [SFinite γ] (τ : Measure Y) [SFinite τ] [τ.IsAddRightInvariant]

omit [BorelSpace Ω] [R1Space Ω] [SecondCountableTopology Y] in
lemma measurePreserving_labelTranslate (u : Y) :
    MeasurePreserving (labelTranslate u) (γ.prod τ) (γ.prod τ) := by
  exact (MeasurePreserving.id γ).prod (measurePreserving_add_right τ u)

omit [MeasurableSpace Ω] [BorelSpace Ω] [R1Space Ω]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
lemma continuous_labelTranslate : Continuous (labelTranslate (Ω := Ω) (Y := Y)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Y × (Ω × Y) => (z.2.1, z.2.2 + z.1))
  fun_prop

variable [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)]

lemma tendsto_eLpNorm_labelTranslate_sub {F : Ω × Y → ℝ} (hF : MemLp F 1 (γ.prod τ)) :
    Tendsto (fun u : Y => eLpNorm (fun x => F (x.1, x.2 + u) - F x) 1 (γ.prod τ))
      (𝓝 0) (𝓝 0) := by
  let f := hF.toLp F
  let g := fun u => Lp.compMeasurePreserving (labelTranslate u)
    (measurePreserving_labelTranslate γ τ u) f
  have hc : Continuous g := continuous_const.compMeasurePreservingLp continuous_labelTranslate
    (measurePreserving_labelTranslate γ τ) (by simp)
  have hg0 : g 0 = f := by
    have he : (labelTranslate (Ω := Ω) (0:Y) : Ω × Y → Ω × Y) = id := by
      ext x <;> simp [labelTranslate]
    dsimp only [g]
    simp only [he, Lp.compMeasurePreserving_id_apply]
  have ht : Tendsto g (𝓝 0) (𝓝 (hF.toLp F)) := by
    simpa only [hg0] using hc.tendsto 0
  have hl := (Lp.tendsto_Lp_iff_tendsto_eLpNorm g F hF).mp ht
  apply hl.congr'
  apply Eventually.of_forall
  intro u
  apply eLpNorm_congr_ae
  have he := (Lp.coeFn_compMeasurePreserving f (measurePreserving_labelTranslate γ τ u)).trans
    ((measurePreserving_labelTranslate γ τ u).quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp)
  filter_upwards [he] with x hx
  exact congrArg (fun t => t - F x) hx

omit [BorelSpace Ω] [R1Space Ω] [SecondCountableTopology Y]
  [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)] in
lemma eLpNorm_labelTranslate_sub_le {F : Ω × Y → ℝ} (hF : MemLp F 1 (γ.prod τ)) (u : Y) :
    eLpNorm (fun x => F (x.1,x.2+u) - F x) 1 (γ.prod τ) ≤
      eLpNorm F 1 (γ.prod τ) + eLpNorm F 1 (γ.prod τ) := by
  have hp := measurePreserving_labelTranslate γ τ u
  have he := eLpNorm_comp_measurePreserving (p := (1:ℝ≥0∞)) hF.aestronglyMeasurable hp
  exact (eLpNorm_sub_le (hF.aestronglyMeasurable.comp_quasiMeasurePreserving hp.quasiMeasurePreserving) hF.aestronglyMeasurable le_rfl).trans_eq
    (congrArg (fun t => t + eLpNorm F 1 (γ.prod τ)) he)
variable [NormedSpace ℝ Y]

omit [BorelSpace Ω] [R1Space Ω]
  [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)] in
lemma integrable_translate_product (κ : Measure Y) [IsProbabilityMeasure κ]
    {F : Ω × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 1 (γ.prod τ)) (δ : ℝ) :
    Integrable (fun z : Y × (Ω × Y) => F (z.2.1,z.2.2 + δ • z.1))
      (κ.prod (γ.prod τ)) := by
  refine ⟨(by fun_prop : Measurable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ (by fun_prop)]
  have he (u : Y) : (∫⁻ x, ‖F (x.1,x.2 + δ • u)‖ₑ ∂γ.prod τ) =
      eLpNorm F 1 (γ.prod τ) := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable
      (measurePreserving_labelTranslate γ τ (δ • u))
  simp_rw [he]
  simpa using hF.eLpNorm_lt_top

omit [BorelSpace Ω] [R1Space Ω]
  [(γ.prod τ).InnerRegularCompactLTTop] [IsLocallyFiniteMeasure (γ.prod τ)] in
lemma eLpNorm_averageTranslate_sub_le (κ : Measure Y) [IsProbabilityMeasure κ]
    {F : Ω × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 1 (γ.prod τ)) (δ : ℝ) :
    eLpNorm (fun x => averageTranslate κ δ F x - F x) 1 (γ.prod τ) ≤
      ∫⁻ u, eLpNorm (fun x => F (x.1,x.2 + δ • u) - F x) 1 (γ.prod τ) ∂κ := by
  have haverage : StronglyMeasurable (averageTranslate κ δ F) :=
    ((show Measurable (fun pair : (Ω × Y) × Y =>
      F (pair.1.1, pair.1.2 + δ • pair.2)) from by fun_prop).stronglyMeasurable).integral_prod_right'
  rw [eLpNorm_one_eq_lintegral_enorm
    (f := fun point => averageTranslate κ δ F point - F point)]
  have hi := (integrable_translate_product γ τ κ hFm hF δ).prod_left_ae
  calc
    _ ≤ ∫⁻ x, ∫⁻ u, ‖F (x.1,x.2 + δ • u) - F x‖ₑ ∂κ ∂γ.prod τ := by
      apply lintegral_mono_ae
      filter_upwards [hi] with x hx
      have he : averageTranslate κ δ F x - F x =
          ∫ u, F (x.1,x.2 + δ • u) - F x ∂κ := by
        rw [integral_sub hx (integrable_const (F x)), integral_const]
        simp [averageTranslate]
      rw [he]
      exact enorm_integral_le_lintegral_enorm _
    _ = _ := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      congr 1
      funext u
      exact (eLpNorm_one_eq_lintegral_enorm).symm

lemma tendsto_eLpNorm_averageTranslate_sub (κ : Measure Y) [IsProbabilityMeasure κ]
    {F : Ω × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 1 (γ.prod τ)) :
    Tendsto (fun δ : ℝ => eLpNorm (fun x => averageTranslate κ δ F x - F x)
      1 (γ.prod τ)) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun δ : ℝ => ∫⁻ u, eLpNorm
      (fun x => F (x.1,x.2 + δ • u) - F x) 1 (γ.prod τ) ∂κ)
      (𝓝 0) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := κ) (l := 𝓝 (0:ℝ)) (f := fun _ => 0)
      (fun _ => eLpNorm F 1 (γ.prod τ) + eLpNorm F 1 (γ.prod τ))
      (Eventually.of_forall (fun δ => ?_))
      (Eventually.of_forall (fun δ => Eventually.of_forall (fun u =>
        eLpNorm_labelTranslate_sub_le γ τ hF (δ • u))))
      (by simpa using ENNReal.add_ne_top.mpr ⟨hF.eLpNorm_lt_top.ne, hF.eLpNorm_lt_top.ne⟩)
      (Eventually.of_forall (fun u => ?_))
    · simpa using h
    · have hnorm (translation : Y) :
          eLpNorm (fun point => F (point.1, point.2 + δ • translation) - F point)
            1 (γ.prod τ) =
          ∫⁻ point, ‖F (point.1, point.2 + δ • translation) - F point‖ₑ ∂γ.prod τ :=
        eLpNorm_one_eq_lintegral_enorm
      simp_rw [hnorm]
      exact Measurable.lintegral_prod_right (by fun_prop)
    · exact (tendsto_eLpNorm_labelTranslate_sub γ τ hF).comp
        (by
          have hc : Continuous (fun δ : ℝ => δ • u) := by fun_prop
          simpa using hc.tendsto (0:ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (eLpNorm_averageTranslate_sub_le γ τ κ hFm hF)
end Translation
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_JointL1
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma gaussianPDF_zero_sub_comm (v : ℝ≥0) (a b : ℝ) :
    gaussianPDF 0 v (a-b) = gaussianPDF 0 v (b-a) := by
  simp only [gaussianPDF, gaussianPDFReal, sub_zero]
  congr 4
  ring

lemma GaussianRegularization_eq_toReal {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (m : ℕ) (δ : ℝ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) :
    GaussianRegularization μ m δ x =
      (projectionSmoothing μ (gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩) m x).toReal := by
  let v : ℝ≥0 := ⟨δ^2,sq_nonneg δ⟩
  change (∫ s, ∏ j, gaussianPDFReal 0 v (x.2 j - ⟪s,x.1 j⟫) ∂μ) = _
  have hn : ∀ s : Space d, 0 ≤ ∏ j, gaussianPDFReal 0 v (x.2 j - ⟪s,x.1 j⟫) :=
    fun s => Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)
  have hm : Measurable (fun s : Space d => ∏ j, gaussianPDFReal 0 v (x.2 j - ⟪s,x.1 j⟫)) := by
    fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hn) hm.aestronglyMeasurable]
  unfold projectionSmoothing
  congr 1
  apply lintegral_congr
  intro s
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _)]
  rfl

lemma GaussianRegularization_ae_eq_average {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (m : ℕ)
    (F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ)
    (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hden : (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m) (δ : ℝ) (hδ : δ ≠ 0) :
    GaussianRegularization μ m δ =ᵐ[MatrixLabelReference d m]
      averageTranslate (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) δ F := by
  have he := projectionSmoothing_ae_eq_fiberSmoothing μ m
    (fun x => ENNReal.ofReal (F x)) hF.ennreal_ofReal hden
    (gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩) (measurable_gaussianPDF _ _)
  filter_upwards [he] with x hx
  rw [GaussianRegularization_eq_toReal, hx]
  unfold averageTranslate
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun u => hF0 _))
    ((hF.comp (by fun_prop)).aestronglyMeasurable)]
  congr 1
  change fiberSmoothing volume (fun x => ENNReal.ofReal (F x))
    (fun y : Fin m → ℝ => ∏ j, gaussianPDF 0 _ (y j)) x =
      ∫⁻ u : Fin m → ℝ, ENNReal.ofReal (F (x.1,fun j => x.2 j + δ * u j))
        ∂Measure.pi (fun _ => gaussianReal 0 1)
  rw [lintegral_gaussian_shift_scale m δ hδ x.2 (fun y => ENNReal.ofReal (F (x.1,y)))
    (by fun_prop)]
  apply lintegral_congr
  intro y
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact gaussianPDF_zero_sub_comm _ _ _

lemma memLp_density_of_finite {X : Type*} [MeasurableSpace X]
    (ν₀ η : Measure X) [IsFiniteMeasure η] {F : X → ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hden : ν₀.withDensity (fun x => ENNReal.ofReal (F x)) = η) :
    MemLp F 1 ν₀ := by
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have he : (fun x => ‖F x‖ₑ) = (fun x => ENNReal.ofReal (F x)) := by
    funext x
    exact Real.enorm_eq_ofReal (hF0 x)
  rw [he]
  have he2 := congrArg (fun ν : Measure X => ν Set.univ) hden
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he2
  rw [he2]
  exact measure_lt_top _ _

lemma density_ae_unique_real {X : Type*} [MeasurableSpace X]
    (ν₀ : Measure X) [SigmaFinite ν₀] {F G : X → ℝ}
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hGm : Measurable G) (hG0 : ∀ x, 0 ≤ G x)
    (hden : ν₀.withDensity (fun x => ENNReal.ofReal (F x)) =
      ν₀.withDensity (fun x => ENNReal.ofReal (G x))) : F =ᵐ[ν₀] G := by
  have he := (withDensity_eq_iff_of_sigmaFinite hFm.ennreal_ofReal.aemeasurable
    hGm.ennreal_ofReal.aemeasurable).mp hden
  filter_upwards [he] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hF0 x) (hG0 x)).mp hx

theorem joint_l1 : JointL1Statement := by
  intro d m p hd hm hmd hp β H R hgap hH hR z μ hμ hs hb hac F hFm hF0 hden
  have : IsFiniteMeasure μ := hμ
  have : IsFiniteMeasure (ProjectionLaw μ m) := by unfold ProjectionLaw; infer_instance
  have : SigmaFinite (MatrixLabelReference d m) := by unfold MatrixLabelReference; infer_instance
  have hF := memLp_density_of_finite (MatrixLabelReference d m) (ProjectionLaw μ m) hFm hF0 hden
  constructor
  · have ht := tendsto_eLpNorm_averageTranslate_sub
      (Measure.pi (fun _ : Fin m => stdGaussian (Space d)))
      (volume : Measure (Fin m → ℝ))
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) hFm hF
    apply (ht.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply eLpNorm_congr_ae
    filter_upwards [GaussianRegularization_ae_eq_average μ m F hFm hF0 hden δ
      (ne_of_gt hδ)] with x hx
    exact congrArg (fun t => t - F x) hx.symm
  · obtain ⟨G,hGm,hG0,hGden,hGs,hGnorm⟩ :=
      exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
    have he := density_ae_unique_real (MatrixLabelReference d m) hFm hF0 hGm hG0
      (hden.trans hGden.symm)
    exact (eLpNorm_congr_ae he).symm ▸ hGnorm
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_PointwiseDensity
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma measurable_GaussianRegularization {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (m : ℕ) (δ : ℝ) : Measurable (GaussianRegularization μ m δ) := by
  have he : GaussianRegularization μ m δ = fun x =>
      (projectionSmoothing μ (gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩) m x).toReal :=
    funext (GaussianRegularization_eq_toReal μ m δ)
  rw [he]
  exact (measurable_projectionSmoothing μ _ (measurable_gaussianPDF _ _) m).ennreal_toReal

lemma PointwiseDensity_eq_of_tendsto {d m : ℕ} (μ : Measure (Space d))
    (x : (Fin m → Space d) × (Fin m → ℝ)) {l : ℝ}
    (h : Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x) atTop (𝓝 l)) :
    PointwiseDensity μ m x = l := by
  classical
  unfold PointwiseDensity
  rw [dite_eq_left ⟨l,h⟩]
  exact tendsto_nhds_unique (Classical.choose_spec (show ∃ l : ℝ,
    Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x) atTop (𝓝 l) from ⟨l,h⟩)) h

lemma measurable_PointwiseDensity {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (m : ℕ) : Measurable (PointwiseDensity μ m) := by
  classical
  let S := {x : (Fin m → Space d) × (Fin m → ℝ) | ∃ l : ℝ,
    Tendsto (fun i : ℕ => GaussianRegularization μ m (1/(i:ℝ)) x) atTop (𝓝 l)}
  have hS : MeasurableSet S :=
    measurableSet_exists_tendsto (fun i => measurable_GaussianRegularization μ m _)
  apply measurable_of_tendsto_metrizable
    (f := fun i => S.indicator (GaussianRegularization μ m (1/(i:ℝ))))
    (fun i => (measurable_GaussianRegularization μ m _).indicator hS)
  apply tendsto_pi_nhds.mpr
  intro x
  by_cases hx : x ∈ S
  · rcases hx with ⟨l,hl⟩
    rw [PointwiseDensity_eq_of_tendsto μ x hl]
    simpa only [Set.indicator_of_mem (show x ∈ S from ⟨l,hl⟩)] using hl
  · have he : PointwiseDensity μ m x = 0 := by
      unfold PointwiseDensity
      exact dite_eq_right hx
    rw [he]
    simpa only [Set.indicator_of_notMem hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

lemma GaussianRegularization_nonneg {d : ℕ} (μ : Measure (Space d)) (m : ℕ) (δ : ℝ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : 0 ≤ GaussianRegularization μ m δ x :=
  integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _))

lemma PointwiseDensity_nonneg {d : ℕ} (μ : Measure (Space d)) (m : ℕ)
    (x : (Fin m → Space d) × (Fin m → ℝ)) : 0 ≤ PointwiseDensity μ m x := by
  classical
  unfold PointwiseDensity
  split_ifs with h
  · exact ge_of_tendsto (Classical.choose_spec h)
      (Eventually.of_forall (fun i => GaussianRegularization_nonneg μ m _ x))
  · exact le_rfl
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SphericalProjection
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

section RadialCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radialShrink_mem_ball {c : ℝ} (hc : 0 < c) (v : E) :
    radialShrink c v ∈ Metric.ball 0 1 := by
  have hp : 0 < ‖v‖^2 + c^2 := by positivity
  have hs : 0 < Real.sqrt (‖v‖^2 + c^2) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  rw [Metric.mem_ball, dist_zero_right, radialShrink, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hlt : ‖v‖ < Real.sqrt (‖v‖^2 + c^2) := by nlinarith [sq_pos_of_pos hc]
  simpa [div_eq_mul_inv, mul_comm] using (div_lt_one hs).mpr hlt

lemma radialExpand_shrink {c : ℝ} (hc : 0 < c) (v : E) :
    radialExpand c (radialShrink c v) = v := by
  let t := Real.sqrt (‖v‖^2+c^2)
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t^2 = ‖v‖^2+c^2 := Real.sq_sqrt (by positivity)
  have he : 1 - ⟪radialShrink c v,radialShrink c v⟫ = (c/t)^2 := by
    simp only [radialShrink, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      real_inner_self_eq_norm_sq]
    change 1 - t⁻¹ * (t⁻¹ * ‖v‖^2) = (c/t)^2
    field_simp
    nlinarith [ht2]
  rw [radialExpand, he, Real.sqrt_sq (le_of_lt (div_pos hc ht)), radialShrink,
    smul_smul]
  change (c / (c/t) * t⁻¹) • v = v
  have he' : c / (c/t) * t⁻¹ = 1 := by field_simp
  rw [he', one_smul]

lemma radialExpand_differentiableOn (c : ℝ) :
    DifferentiableOn ℝ (radialExpand (E := E) c) (Metric.ball 0 1) := by
  intro u hu
  have hu' : ‖u‖ < 1 := by simpa using hu
  have hpos : 0 < 1 - ⟪u,u⟫ := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg u]
  apply DifferentiableAt.differentiableWithinAt
  unfold radialExpand
  apply DifferentiableAt.smul
  · simp only [div_eq_mul_inv]
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.inv
    · apply DifferentiableAt.sqrt
      · exact (differentiableAt_const 1).sub
          (DifferentiableAt.inner ℝ differentiableAt_id differentiableAt_id)
      · exact ne_of_gt hpos
    · exact ne_of_gt (Real.sqrt_pos.2 hpos)
  · exact differentiableAt_id

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma radialShrink_preimage_null {c : ℝ} (hc : 0 < c) {s : Set E}
    (hs : volume s = 0) : volume (radialShrink c ⁻¹' s) = 0 := by
  have hn : volume (s ∩ Metric.ball (0:E) 1) = 0 :=
    measure_mono_null Set.inter_subset_left hs
  have hi := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((radialExpand_differentiableOn (E:=E) c).mono Set.inter_subset_right) hn
  apply measure_mono_null _ hi
  intro v hv
  refine ⟨radialShrink c v, ⟨hv, radialShrink_mem_ball hc v⟩, ?_⟩
  exact radialExpand_shrink hc v
end RadialCoordinates

section Projection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma orthogonal_normalized_preimage_null (K : Submodule ℝ E) [Nontrivial Kᗮ]
    {s : Set K} (hs : MeasurableSet s) (hs0 : volume s = 0) :
    volume {x : E | ‖x‖⁻¹ • K.orthogonalProjectionOnto x ∈ s} = 0 := by
  let e : (Kᗮ × K) ≃ₗ[ℝ] E :=
    (LinearEquiv.prodComm ℝ Kᗮ K).trans (K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal)
  let t : Set (Kᗮ × K) := {x | radialShrink ‖x.1‖ x.2 ∈ s}
  have ht : MeasurableSet t := by
    apply hs.preimage
    dsimp [radialShrink]
    fun_prop
  have ht0 : ((volume : Measure Kᗮ).prod (volume : Measure K)) t = 0 := by
    rw [Measure.prod_apply ht]
    rw [← lintegral_zero (μ := (volume : Measure Kᗮ))]
    apply lintegral_congr_ae
    have hk : ∀ᵐ k : Kᗮ ∂volume, k ≠ 0 := by
      simpa only [Ne, ← Set.mem_singleton_iff] using
        (measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0:Kᗮ)))
    filter_upwards [hk] with k hk
    exact radialShrink_preimage_null (norm_pos_iff.mpr hk) hs0
  have hn : MeasurableSet {x : E | ‖x‖⁻¹ • K.orthogonalProjectionOnto x ∈ s} := by
    apply hs.preimage
    exact measurable_id.norm.inv.smul K.orthogonalProjectionOnto.continuous.measurable
  have hnt : e ⁻¹' {x : E | ‖x‖⁻¹ • K.orthogonalProjectionOnto x ∈ s} = t := by
    ext x
    have hp : K.orthogonalProjectionOnto (e x) = x.2 := by
      change K.orthogonalProjectionOnto ((x.2:E)+(x.1:E)) = x.2
      rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.1.property, add_zero]
    have hnorm : ‖e x‖ = Real.sqrt (‖x.2‖^2 + ‖x.1‖^2) := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x.2:E) (x.1:E)
        (Submodule.inner_right_of_mem_orthogonal x.2.property x.1.property)
      have he : ‖e x‖^2 = ‖x.2‖^2 + ‖x.1‖^2 := by
        change ‖(x.2:E)+(x.1:E)‖^2 = _
        simpa only [pow_two, Submodule.norm_coe] using h
      rw [← he, Real.sqrt_sq (norm_nonneg _)]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hp, hnorm, t, radialShrink]
  let : ((((volume : Measure Kᗮ).prod (volume : Measure K)).map e)).IsAddHaarMeasure :=
    Measure.MapLinearEquiv.isAddHaarMeasure _ e
  have heac : (volume : Measure E) ≪
      (((volume : Measure Kᗮ).prod (volume : Measure K)).map e) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply heac
  rw [Measure.map_apply (f := e) e.toContinuousLinearEquiv.continuous.measurable hn, hnt, ht0]

lemma sphere_projection_ac (K : Submodule ℝ E) [Nontrivial E] [Nontrivial Kᗮ] :
    ((sphereLaw (E:=E)).map (fun x => K.orthogonalProjectionOnto x.val)) ≪
      (volume : Measure K) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hm : Measurable (fun x : Metric.sphere (0:E) 1 => K.orthogonalProjectionOnto x.val) :=
    K.orthogonalProjectionOnto.continuous.measurable.comp measurable_subtype_coe
  rw [Measure.map_apply hm hs, sphereLaw_apply (hm hs)]
  have hn := orthogonal_normalized_preimage_null K hs hs0
  have hcone : volume (Set.Ioo (0:ℝ) 1 •
      (Subtype.val '' ((fun x : Metric.sphere (0:E) 1 => K.orthogonalProjectionOnto x.val) ⁻¹' s))) = 0 := by
    apply measure_mono_null _ hn
    rintro _ ⟨r, hr, _, ⟨x, hx, rfl⟩, rfl⟩
    change ‖r • x.val‖⁻¹ • K.orthogonalProjectionOnto (r • x.val) ∈ s
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1,
      mem_sphere_zero_iff_norm.mp x.property, mul_one, map_smul, smul_smul,
      inv_mul_cancel₀ hr.1.ne', one_smul]
    exact hx
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet]
  rw [measure_mono_null Set.inter_subset_left hcone, mul_zero]

lemma sphere_rows_ac [Nontrivial E] {m : ℕ} (A : Fin m → E)
    (hA : LinearIndependent ℝ A) (hm : m < Module.finrank ℝ E) :
    ((sphereLaw (E:=E)).map
      (fun x : Metric.sphere (0:E) 1 => fun j => ⟪x.val,A j⟫)) ≪
      (volume : Measure (Fin m → ℝ)) := by
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range A)
  have hd : Module.finrank ℝ K = m := by
    simpa only [K, Fintype.card_fin] using finrank_span_eq_card hA
  have hK : K ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hd
    omega
  have : Nontrivial Kᗮ := Submodule.nontrivial_iff_ne_bot.mpr
    (fun h => hK (Submodule.orthogonal_eq_bot_iff.mp h))
  let L : K →ₗ[ℝ] (Fin m → ℝ) :=
    LinearMap.pi (fun j => (innerSL ℝ (A j)).toLinearMap.comp K.subtype)
  have hLi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro x hx
    have hle : K ≤ (innerSL ℝ (x:E)).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change ⟪(x:E),A j⟫ = 0
      have hj := congrFun hx j
      change ⟪A j,(x:E)⟫ = 0 at hj
      rwa [real_inner_comm]
    have hz : ⟪(x:E),(x:E)⟫ = 0 := hle x.property
    exact Subtype.ext (inner_self_eq_zero.mp hz)
  have hdim : Module.finrank ℝ K = Module.finrank ℝ (Fin m → ℝ) := by
    simpa using hd
  let e : K ≃ₗ[ℝ] (Fin m → ℝ) :=
    LinearEquiv.ofBijective L ⟨hLi,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLi⟩
  have he : (fun x : Metric.sphere (0:E) 1 => fun j => ⟪x.val,A j⟫) =
      e ∘ (fun x : Metric.sphere (0:E) 1 => K.orthogonalProjectionOnto x.val) := by
    funext x j
    change ⟪x.val,A j⟫ = ⟪A j,(K.orthogonalProjectionOnto x.val:E)⟫
    have hp := K.inner_orthogonalProjectionOnto_eq_of_mem_left
      ⟨A j, Submodule.subset_span ⟨j,rfl⟩⟩ x.val
    change ⟪A j,(K.orthogonalProjectionOnto x.val:E)⟫ = ⟪A j,x.val⟫ at hp
    rw [hp, real_inner_comm]
  rw [he, ← Measure.map_map (f := fun x : Metric.sphere (0:E) 1 =>
    K.orthogonalProjectionOnto x.val) (g := e)
    e.toContinuousLinearEquiv.continuous.measurable (by fun_prop)]
  apply ((sphere_projection_ac K).map
    (show Measurable e from e.toContinuousLinearEquiv.continuous.measurable)).trans
  let : ((volume : Measure K).map e).IsAddHaarMeasure :=
    Measure.MapLinearEquiv.isAddHaarMeasure _ e
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _
end Projection

theorem spherical_projection_ac {d m : ℕ} (hd : 2 ≤ d) (hm : m < d)
    (A : Fin m → Space d) (hA : LinearIndependent ℝ A)
    (μ : Measure (Space d)) (hμ : μ ≪ UniformSphere d) :
    μ.map (fun s => fun j => ⟪s,A j⟫) ≪ (volume : Measure (Fin m → ℝ)) := by
  have : NeZero d := ⟨by omega⟩
  apply (hμ.map (by fun_prop)).trans
  have h := sphere_rows_ac A hA (by simpa using hm)
  simpa only [UniformSphere, Kernel.UniformSphere, sphereLaw, Measure.map_map (by fun_prop :
    Measurable (fun s : Space d => fun j => ⟪s,A j⟫)) measurable_subtype_coe,
    Function.comp_def] using h
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_FiberDensity
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma piGaussianConvolution_eq {m : ℕ} (ν : Measure (Fin m → ℝ)) (δ : ℝ) (y : Fin m → ℝ) :
    PiGaussianConvolution ν δ y =
      GaussianConvolution (ν.map (WithLp.toLp 2)) δ (WithLp.toLp 2 y) := by
  unfold GaussianConvolution
  rw [integral_map (WithLp.measurable_toLp 2 (Fin m → ℝ)).aemeasurable
    ((show Continuous (fun x : Space m => GaussianKernel m δ (WithLp.toLp 2 y - x)) from
      (gaussianKernel_continuous m δ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)]
  rfl

lemma ae_tendsto_piGaussianConvolution {m : ℕ} (hm : 1 ≤ m) (ν : Measure (Fin m → ℝ))
    [IsFiniteMeasure ν] (hν : ν ≪ volume) :
    ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), Tendsto (fun δ : ℝ => PiGaussianConvolution ν δ y)
      (𝓝[>] (0:ℝ)) (𝓝 ((ν.rnDeriv volume y).toReal)) := by
  let e := MeasurableEquiv.toLp 2 (Fin m → ℝ)
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin m)
  have hac : ν.map e ≪ volume := by
    rw [← hp.map_eq]
    exact hν.map e.measurable
  have ht := ae_tendsto_gaussianConvolution hm (ν.map e) hac
  have ht' : ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)),
      Tendsto (fun δ : ℝ => GaussianConvolution (ν.map e) δ (e y))
        (𝓝[>] (0:ℝ)) (𝓝 (((ν.map e).rnDeriv volume (e y)).toReal)) := by
    have ht0 : ∀ᵐ y ∂(volume.map e),
        Tendsto (fun δ : ℝ => GaussianConvolution (ν.map e) δ y)
          (𝓝[>] (0:ℝ)) (𝓝 (((ν.map e).rnDeriv volume y).toReal)) := by
      rwa [hp.map_eq]
    exact e.measurableEmbedding.ae_map_iff.mp ht0
  have hRN := e.measurableEmbedding.rnDeriv_map ν volume
  rw [hp.map_eq] at hRN
  filter_upwards [ht', hRN] with y hy hyRN
  rw [hyRN] at hy
  simpa only [piGaussianConvolution_eq, e, MeasurableEquiv.coe_toLp] using hy

lemma GaussianRegularization_eq_convolution {d m : ℕ} (μ : Measure (Space d))
    (A : Fin m → Space d) (δ : ℝ) (y : Fin m → ℝ) :
    GaussianRegularization μ m δ (A,y) =
      PiGaussianConvolution (μ.map (fun s => fun j => ⟪s,A j⟫)) δ y := by
  unfold PiGaussianConvolution
  rw [integral_map (by fun_prop)
    (((show Continuous (fun x : Fin m → ℝ => ∏ j,
      gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j - x j)) from
      by unfold gaussianPDFReal; fun_prop)).aestronglyMeasurable)]
  rfl

lemma ae_tendsto_GaussianRegularization {d m : ℕ} (hm : 1 ≤ m) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (A : Fin m → Space d)
    (hA : μ.map (fun s => fun j => ⟪s,A j⟫) ≪ (volume : Measure (Fin m → ℝ))) :
    ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), Tendsto
      (fun δ : ℝ => GaussianRegularization μ m δ (A,y)) (𝓝[>] (0:ℝ))
      (𝓝 (((μ.map (fun s => fun j => ⟪s,A j⟫)).rnDeriv volume y).toReal)) := by
  simpa only [GaussianRegularization_eq_convolution] using
    ae_tendsto_piGaussianConvolution hm (μ.map (fun s => fun j => ⟪s,A j⟫)) hA

lemma reciprocal_nat_tendsto :
    Tendsto (fun i : ℕ => 1/(i:ℝ)) atTop (𝓝[>] (0:ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi
  change 0 < 1/(i:ℝ)
  positivity

lemma pointwiseDensity_fiber {d m : ℕ} (hm : 1 ≤ m) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (A : Fin m → Space d)
    (hA : μ.map (fun s => fun j => ⟪s,A j⟫) ≪ (volume : Measure (Fin m → ℝ))) :
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      μ.map (fun s => fun j => ⟪s,A j⟫) := by
  let ν := μ.map (fun s => fun j => ⟪s,A j⟫)
  have he : (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =ᵐ[volume]
      ν.rnDeriv volume := by
    filter_upwards [ae_tendsto_GaussianRegularization hm μ A hA, ν.rnDeriv_lt_top volume]
      with y hy hyfin
    rw [PointwiseDensity_eq_of_tendsto μ (A,y) (hy.comp reciprocal_nat_tendsto)]
    exact ENNReal.ofReal_toReal hyfin.ne
  rw [withDensity_congr_ae he]
  exact Measure.withDensity_rnDeriv_eq _ _ hA

lemma pointwiseDensity_fullRank {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) (hmd : m < d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (hμ : μ ≪ UniformSphere d)
    (A : Fin m → Space d) (hA : LinearIndependent ℝ A) :
    (volume : Measure (Fin m → ℝ)).withDensity
      (fun y => ENNReal.ofReal (PointwiseDensity μ m (A,y))) =
      μ.map (fun s => fun j => ⟪s,A j⟫) :=
  pointwiseDensity_fiber hm μ A (spherical_projection_ac hd hmd A hA μ hμ)
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_DensityUniqueness
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma piGaussianConvolution_withDensity {m : ℕ} (F : (Fin m → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (δ : ℝ) (y : Fin m → ℝ) :
    PiGaussianConvolution (volume.withDensity F) δ y =
      (∫⁻ x, (∏ j, gaussianPDF 0 ⟨δ^2,sq_nonneg δ⟩ (y j-x j)) * F x).toReal := by
  unfold PiGaussianConvolution
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => Finset.prod_nonneg (fun j _ => gaussianPDFReal_nonneg _ _ _)))
    ((show Continuous (fun x : Fin m → ℝ => ∏ j,
      gaussianPDFReal 0 ⟨δ^2,sq_nonneg δ⟩ (y j-x j)) from
      by unfold gaussianPDFReal; fun_prop).aestronglyMeasurable),
    lintegral_withDensity_eq_lintegral_mul _ hF (by fun_prop)]
  congr 1
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ =>
    gaussianPDFReal_nonneg 0 ⟨δ^2,sq_nonneg δ⟩ (y j-x j)), mul_comm]

lemma ae_tendsto_fiberGaussian {Ω : Type*} [MeasurableSpace Ω] (γ : Measure Ω)
    [SigmaFinite γ] {m : ℕ} (hm : 1 ≤ m)
    (F : Ω × (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hfin : (∫⁻ z, F z ∂γ.prod volume) ≠ ∞) :
    ∀ᵐ z ∂γ.prod volume, Tendsto
      (fun i : ℕ => (fiberSmoothing volume F
        (fun y : Fin m → ℝ => ∏ j, gaussianPDF 0
          ⟨(1/(i:ℝ))^2,sq_nonneg _⟩ (y j)) z).toReal)
      atTop (𝓝 (F z).toReal) := by
  have hmeas (i : ℕ) : Measurable (fun z => (fiberSmoothing volume F
      (fun y : Fin m → ℝ => ∏ j, gaussianPDF 0
        ⟨(1/(i:ℝ))^2,sq_nonneg _⟩ (y j)) z).toReal) :=
    (measurable_fiberSmoothing volume hF (by fun_prop)).ennreal_toReal
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hmeas hF.ennreal_toReal)]
  have hinner : (∫⁻ A, ∫⁻ y : Fin m → ℝ, F (A,y) ∂volume ∂γ) ≠ ∞ := by
    rwa [← lintegral_prod _ hF.aemeasurable]
  filter_upwards [ae_lt_top (Measurable.lintegral_prod_right
    (show Measurable (fun z : Ω × (Fin m → ℝ) => F (z.1,z.2)) from hF)) hinner] with A hA
  let ν : Measure (Fin m → ℝ) := volume.withDensity (fun y => F (A,y))
  have hFA : Measurable (fun y : Fin m → ℝ => F (A,y)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hA.ne
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  have hRN := Measure.rnDeriv_withDensity volume hFA
  filter_upwards [ae_tendsto_piGaussianConvolution hm ν hac, hRN] with y hy hyRN
  rw [hyRN] at hy
  convert hy.comp reciprocal_nat_tendsto using 1
  ext i
  exact (piGaussianConvolution_withDensity (fun y => F (A,y)) hFA _ y).symm

lemma pointwiseDensity_ae_eq {d m : ℕ} (hm : 1 ≤ m) (μ : Measure (Space d))
    [IsFiniteMeasure μ] (F : ((Fin m → Space d) × (Fin m → ℝ)) → ℝ)
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hden : (MatrixLabelReference d m).withDensity (fun x => ENNReal.ofReal (F x)) =
      ProjectionLaw μ m) :
    PointwiseDensity μ m =ᵐ[MatrixLabelReference d m] F := by
  have hfin : (∫⁻ z, ENNReal.ofReal (F z) ∂MatrixLabelReference d m) ≠ ∞ := by
    have he := congrArg (fun ν => ν Set.univ) hden
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
    rw [he]
    let : IsFiniteMeasure (ProjectionLaw μ m) := by unfold ProjectionLaw; infer_instance
    exact measure_ne_top _ _
  have ht := ae_tendsto_fiberGaussian
    (Measure.pi (fun _ : Fin m => stdGaussian (Space d))) hm
    (fun x => ENNReal.ofReal (F x)) hFm.ennreal_ofReal hfin
  have he (i : ℕ) := projectionSmoothing_ae_eq_fiberSmoothing μ m
    (fun x => ENNReal.ofReal (F x)) hFm.ennreal_ofReal hden
    (gaussianPDF 0 ⟨(1/(i:ℝ))^2,sq_nonneg _⟩) (measurable_gaussianPDF _ _)
  filter_upwards [ht, ae_all_iff.mpr he] with x hx hxe
  apply PointwiseDensity_eq_of_tendsto
  rw [ENNReal.toReal_ofReal (hF0 x)] at hx
  convert hx using 1
  ext i
  rw [GaussianRegularization_eq_toReal μ m _, hxe i]
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_StochasticContinuation
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
section Stochastic
variable {J X : Type*} [Fintype J] {d : ℕ}

lemma measurable_stochRoute {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a)) (n k : ℕ) (j w : J) :
    Measurable (fun x => stochRoute δ n k j x w) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    apply Finset.measurable_sum _
    intro a _
    exact ((hδ (n+1) j a).comp (by fun_prop)).mul ((ih (n+1) a).comp (by fun_prop))

lemma stochRoute_sum_le_one {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    (hδ : ∀ n j obs, ∑ a, δ n j obs a ≤ 1) (n k : ℕ) (j : J)
    (x : (Fin k → Space d) × (Fin k → ℝ)) : ∑ w, stochRoute δ n k j x w ≤ 1 := by
  classical
  induction k generalizing n j with
  | zero => simp [stochRoute]
  | succ k ih =>
    simp only [stochRoute]
    rw [Finset.sum_comm]
    calc
      _ = ∑ a, δ (n+1) j (x.1 0,x.2 0) a *
        (∑ w, stochRoute δ (n+1) k a (Fin.tail x.1,Fin.tail x.2) w) := by simp [Finset.mul_sum]
      _ ≤ ∑ a, δ (n+1) j (x.1 0,x.2 0) a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right' (ih (n+1) a _))
      _ ≤ 1 := hδ _ _ _

lemma measurable_stochCont [MeasurableSpace X] {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    {w : ℕ → J → X → ℝ≥0∞} {ι : X → Space d}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (hw : ∀ n j, Measurable (w n j)) (hι : Measurable ι) (n k : ℕ) (j : J) :
    Measurable (stochCont δ w ι n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact Finset.measurable_sum _ (fun a _ =>
      ((hδ (n+1) j a).comp (by fun_prop)).mul ((ih (n+1) a).comp measurable_snd))

lemma stochCont_le_one {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    {w : ℕ → J → X → ℝ≥0∞} (ι : X → Space d)
    (hδ : ∀ n j obs, ∑ a, δ n j obs a ≤ 1)
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : X) :
    stochCont δ w ι n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    apply (lintegral_mono (fun x => (Finset.sum_le_sum
      (fun a _ => mul_le_of_le_one_right' (ih (n+1) a))).trans (hδ _ _ _))).trans_eq
    simp

lemma stochCont_unroll {δ : ℕ → J → (Space d × ℝ) → J → ℝ≥0∞}
    {w : ℕ → J → X → ℝ≥0∞} (ι : X → Space d)
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (n m k : ℕ) (j : J) (s : X) :
    stochCont δ w ι n (m+k) j s =
      ∫⁻ A : Fin m → Space d, ∑ a, stochRoute δ n m j (A,fun i => ⟪ι s,A i⟫) a *
        stochCont δ w ι (n+m) k a s ∂Measure.pi (fun _ => stdGaussian (Space d)) := by
  classical
  induction m generalizing n j with
  | zero => simp [stochRoute]
  | succ m ih =>
    rw [Nat.succ_add, stochCont]
    simp_rw [ih]
    have hf : Measurable (fun A : Fin (m+1) → Space d => ∑ a,
        stochRoute δ n (m+1) j (A,fun i => ⟪ι s,A i⟫) a *
          stochCont δ w ι (n+(m+1)) k a s) := by
      exact Finset.measurable_sum _ (fun a _ =>
        ((measurable_stochRoute hδ n (m+1) j a).comp (by fun_prop)).mul measurable_const)
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    have hm (a : J) : Measurable (fun A : Fin m → Space d => ∑ b,
        stochRoute δ (n+1) m a (A,fun i => ⟪ι s,A i⟫) b *
          stochCont δ w ι (n+1+m) k b s) := by
      exact Finset.measurable_sum _ (fun b _ =>
        ((measurable_stochRoute hδ (n+1) m a b).comp (by fun_prop)).mul measurable_const)
    simp_rw [← lintegral_const_mul _ (hm _)]
    rw [← lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
    apply lintegral_congr
    intro A
    simp only [stochRoute, Fin.cons_zero, Fin.tail_cons]
    have het : Fin.tail (fun i : Fin (m+1) => ⟪ι s,(Fin.cons x A : Fin (m+1) → Space d) i⟫) =
        (fun i => ⟪ι s,A i⟫) := rfl
    rw [het]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    congr 1
    funext a
    congr 1
    funext b
    simp [Nat.add_comm, Nat.add_left_comm]

end Stochastic
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelEvaluation
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma measurable_chordTest (ε : ℝ) : Measurable (chordTest (d := d) ε) := by
  apply Measurable.indicator measurable_const
  exact measurableSet_le (by fun_prop) measurable_const
lemma angleTest_le_one (ε : ℝ) (x : Sphere d × Sphere d) : angleTest ε x ≤ 1 := by
  unfold angleTest
  split <;> simp
lemma chordTest_le_one (ε : ℝ) (x : Sphere d × Sphere d) : chordTest ε x ≤ 1 := by
  exact Set.indicator_le_self' (fun _ _ => bot_le) x
lemma outputTest_measurable {f : Sphere d × Sphere d → ℝ≥0∞} (hf : Measurable f)
    (t : ℕ) (j : State M) : Measurable (K.outputTest f t j) := by
  exact (show Measurable (Function.uncurry (fun s v => f (s,v))) from hf).lintegral_prod_right
lemma outputTest_le_one {f : Sphere d × Sphere d → ℝ≥0∞} (hf : ∀ x, f x ≤ 1)
    (t : ℕ) (j : State M) (s : Sphere d) : K.outputTest f t j s ≤ 1 := by
  exact (lintegral_mono (fun v => hf (s,v))).trans_eq (by simp)

lemma marginal_sum (n : ℕ) (j : State M) (obs : Vector d × ℝ) :
    ∑ a, K.marginal n j obs a = 1 := by
  simp only [marginal]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type]
  exact K.transition_sum n j obs
lemma marginal_measurable (hK : K.Borel) (n : ℕ) (j a : State M) :
    Measurable (fun obs => K.marginal n j obs a) := by
  exact Finset.measurable_sum _ (fun b _ => hK n j (b,a))

section Evaluation
variable {X : Type*} [MeasurableSpace X]
variable (w : ℕ → State M → X → ℝ≥0∞) (ι : X → Vector d)

lemma measurable_eval (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (n k : ℕ) (j : State M) :
    Measurable (fun z : X × Observations d k => K.eval w n k j z.1 z.2) := by
  induction k generalizing n j with
  | zero => exact (hw n j).comp measurable_fst
  | succ k ih =>
    apply Finset.measurable_sum _
    intro a _
    apply ((hK (n+1) j a).comp (by fun_prop)).mul
    cases a with
    | mk b a =>
      cases b
      · exact (ih (n+1) a).comp (measurable_fst.prodMk
          (Measurable.of_eval (fun index => (measurable_pi_apply index.succ).comp measurable_snd)))
      · exact (hw (n+1) a).comp measurable_fst

omit [MeasurableSpace X] in
lemma eval_le_one (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : State M)
    (s : X) (obs : Observations d k) : K.eval w n k j s obs ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    apply (Finset.sum_le_sum (fun a _ => mul_le_of_le_one_right' ?_)).trans_eq
      (K.transition_sum (n+1) j (obs 0))
    split
    · exact hw _ _ _
    · exact ih _ _ _

omit [MeasurableSpace X] in
lemma pathValue_le_one (hw : ∀ n j s, w n j s ≤ 1) (s : X) (obs : Observations d T) :
    K.pathValue w s obs ≤ 1 := by
  apply (Finset.sum_le_sum (fun a _ => mul_le_of_le_one_right' ?_)).trans_eq K.initial_sum
  split
  · exact hw _ _ _
  · exact K.eval_le_one w hw _ _ _ _ _

omit [MeasurableSpace X] in
lemma cont_le_forced_sum (hK : K.Borel) (n k : ℕ) (j : State M) (s : X) :
    K.cont w ι n k j s ≤ ∑ r ∈ Finset.range (k+1),
      MemoryPrecision.stochCont K.marginal w ι n r j s := by
  classical
  induction k generalizing n j with
  | zero => simp [cont, MemoryPrecision.stochCont]
  | succ k ih =>
    let V (a : State M) := ∑ r ∈ Finset.range (k+1),
      MemoryPrecision.stochCont K.marginal w ι (n+1) r a s
    have hwV (a : State M) : w (n+1) a s ≤ V a := by
      simpa [MemoryPrecision.stochCont] using
        (Finset.single_le_sum (fun r _ => bot_le (a := MemoryPrecision.stochCont K.marginal w ι (n+1) r a s))
          (show 0 ∈ Finset.range (k+1) by simp))
    calc
      _ ≤ ∫⁻ x, ∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a * V a.2
          ∂stdGaussian (Vector d) := lintegral_mono (fun x => Finset.sum_le_sum (fun a _ => by
            apply mul_le_mul' le_rfl
            split
            · exact hwV a.2
            · exact ih (n+1) a.2))
      _ = ∑ r ∈ Finset.range (k+1), MemoryPrecision.stochCont K.marginal w ι n (r+1) j s := by
        simp only [MemoryPrecision.stochCont]
        have hm (r : ℕ) : Measurable (fun x : Vector d => ∑ a,
            K.marginal (n+1) j (x,⟪ι s,x⟫) a *
              MemoryPrecision.stochCont K.marginal w ι (n+1) r a s) :=
          Finset.measurable_sum _ (fun a _ =>
            ((K.marginal_measurable hK (n+1) j a).comp (by fun_prop)).mul measurable_const)
        rw [← lintegral_finsetSum _ (fun r _ => hm r)]
        apply lintegral_congr
        intro x
        simp only [V, Finset.mul_sum, Fintype.sum_prod_type, marginal, Finset.sum_mul]
        rw [Finset.sum_comm]
        conv_lhs =>
          arg 2
          ext a
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      _ ≤ ∑ r ∈ Finset.range (k+1+1), MemoryPrecision.stochCont K.marginal w ι n r j s := by
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from zero_le)

end Evaluation
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SphereCaps
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

lemma real_terminal_cap {d : ℕ} (hd : 1 ≤ d) (y z : Space d)
    {ε r α : ℝ} (hε : 0 < ε) (hr : 0 < r) (hα : 0 ≤ α) (hαn : α ≤ (d:ℝ)-1) :
    ((ambientSphereLaw (E := Space d)).restrict (Metric.closedBall y ε)) (Metric.closedBall z r) ≤
      ENNReal.ofReal ((3*4^d:ℝ) * ε^((d:ℝ)-1-α) * r^α) := by
  let : NeZero d := ⟨by omega⟩
  have hn : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  have hs : 0 ≤ (d:ℝ)-1-α := sub_nonneg.mpr hαn
  have he (t : ℝ) (ht : 0 < t) : t^(d-1) = t^((d:ℝ)-1-α)*t^α := by
    rw [← Real.rpow_add ht, sub_add_cancel, ← hn, Real.rpow_natCast]
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · calc
      _ ≤ ambientSphereLaw (E := Space d) (Metric.closedBall z r) := measure_mono Set.inter_subset_left
      _ ≤ ENNReal.ofReal ((3*4^d:ℝ)*r^(d-1)) := by
        simpa [ENNReal.ofReal_mul, finrank_euclideanSpace_fin] using
          ambientSphereLaw_closedBall (E := Space d) z hr (d-1) (by simp)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [he r hr, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le h hs) (by positivity)) (by positivity)
  · calc
      _ ≤ ambientSphereLaw (E := Space d) (Metric.closedBall y ε) := measure_mono Set.inter_subset_right
      _ ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
        simpa [ENNReal.ofReal_mul, finrank_euclideanSpace_fin] using
          ambientSphereLaw_closedBall (E := Space d) y hε (d-1) (by simp)
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [he ε hε, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hε.le (le_of_not_ge h) hα) (by positivity)

lemma sphere_cap_real_mass {d : ℕ} (hd : 1 ≤ d) (y : Space d) {ε α : ℝ}
    (hε : 0 < ε) (hα : 0 ≤ α) (hαn : α ≤ (d:ℝ)-1) :
    SphereBallBound (fun s => capWeight y ε s.val) ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)) α := by
  intro z r hr
  change (∫⁻ s in Subtype.val ⁻¹' Metric.closedBall z r,
    capWeight y ε s.val ∂sphereLaw) ≤ _
  rw [← setLIntegral_map Metric.isClosed_closedBall.measurableSet (measurable_capWeight y ε)
    measurable_subtype_coe]
  change (∫⁻ s in Metric.closedBall z r, capWeight y ε s ∂ambientSphereLaw) ≤ _
  rw [← withDensity_apply _ Metric.isClosed_closedBall.measurableSet]
  change ((ambientSphereLaw (E := Space d)).withDensity
    ((Metric.closedBall y ε).indicator 1)) (Metric.closedBall z r) ≤ _
  rw [withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  exact real_terminal_cap hd y z hε hr hα hαn

lemma sphere_mass_bound {d : ℕ} {h : Sphere d → ℝ≥0∞} {H α : ℝ}
    (hh : SphereBallBound h H α) : (∫⁻ s, h s ∂SpherePrior d) ≤ ENNReal.ofReal H := by
  have he : {s : Sphere d | dist s.val (0:Space d) ≤ 1} = Set.univ := by
    ext s
    simp [dist_zero_right]
  simpa [SphereBallBound, he] using hh 0 1 zero_lt_one

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression

namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma chordTest_eq_cap (ε : ℝ) (s v : MemoryPrecision.Kernel.Sphere d) :
    chordTest ε (s,v) = capWeight v.val ε s.val := by
  classical
  change (if dist v.val s.val ≤ ε then 1 else 0) =
    (if dist s.val v.val ≤ ε then 1 else 0)
  rw [dist_comm]

lemma output_chord_sphere_local (hd : 1 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hα : 0 ≤ α) (hαn : α ≤ (d:ℝ)-1) (t : ℕ) (j : MemoryPrecision.Kernel.State M) :
    SphereBallBound (K.outputTest (chordTest ε) t j)
      ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)) α := by
  have : NeZero d := ⟨by omega⟩
  intro z r hr
  change (∫⁻ s in {s : MemoryPrecision.Kernel.Sphere d | dist s.val z ≤ r},
    ∫⁻ v, chordTest ε (s,v) ∂K.output t j ∂UniformSphere d) ≤ _
  have hm : Measurable (Function.uncurry (fun s v : MemoryPrecision.Kernel.Sphere d => chordTest ε (s,v))) :=
    measurable_chordTest ε
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hb (v : MemoryPrecision.Kernel.Sphere d) := sphere_cap_real_mass hd v.val hε hα hαn z r hr
  simp_rw [chordTest_eq_cap]
  exact (lintegral_mono hb).trans_eq (by simp)

lemma output_chord_sphere_total (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (j : MemoryPrecision.Kernel.State M) :
    (∫⁻ s, K.outputTest (chordTest ε) t j s ∂UniformSphere d) ≤
      ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  have h := sphere_mass_bound (K.output_chord_sphere_local hd hε (α := 0) le_rfl (by
    have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith) t j)
  have hn : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  simpa only [UniformSphere, SpherePrior,sub_zero, ← hn, Real.rpow_natCast] using h

lemma angleTest_le_chordTest (ε : ℝ) (x : MemoryPrecision.Kernel.Sphere d × MemoryPrecision.Kernel.Sphere d) :
    angleTest ε x ≤ chordTest ε x := by
  classical
  by_cases ha : Real.arccos ⟪x.2.val,x.1.val⟫ ≤ ε
  · have hc : dist x.2.val x.1.val ≤ ε := (chord_le_arccos x.2 x.1).trans ha
    simp [angleTest, chordTest, ha, hc]
  · simp [angleTest, ha]

lemma eval_mono {X : Type*} {w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞}
    (h : ∀ n j s, w n j s ≤ v n j s) (n k : ℕ) (j : MemoryPrecision.Kernel.State M)
    (s : X) (obs : Observations d k) : K.eval w n k j s obs ≤ K.eval v n k j s obs := by
  induction k generalizing n j with
  | zero => exact h n j s
  | succ k ih =>
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul' le_rfl
    split
    · exact h _ _ _
    · exact ih _ _ _

lemma pathValue_mono {X : Type*} {w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞}
    (h : ∀ n j s, w n j s ≤ v n j s) (s : X) (obs : Observations d T) :
    K.pathValue w s obs ≤ K.pathValue v s obs := by
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul' le_rfl
  split
  · exact h _ _ _
  · exact K.eval_mono h _ _ _ _ _

lemma success_le_chord {Ω : Type*} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) (π : Measure (MemoryPrecision.Kernel.Sphere d)) (ε : ℝ) :
    Success L ρ π ε ≤ ChordSuccess L ρ π ε := by
  apply lintegral_mono
  intro z
  exact (L z.2.1).pathValue_mono (fun n j s => lintegral_mono (fun v => angleTest_le_chordTest ε (s,v))) _ _
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SuccessArithmetic
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma successConstant_one : 1 ≤ SuccessConstant := by
  have h := stepConstant_one
  dsimp [SuccessConstant]
  linarith

lemma stopping_factor_bound {d : ℕ} (hd : 16 ≤ d) (T : ℕ) :
    (T+1:ℝ) ≤ ((2:ℝ)^d)^BlockCount T (d/8) := by
  have hT := blockCount_mul_ge T (by omega : 0 < d/8)
  have hp : d/8 ≤ d := Nat.div_le_self _ _
  have hTd : T ≤ d * BlockCount T (d/8) := by nlinarith
  have htwo : (T+1:ℕ) ≤ 2^T := Nat.lt_two_pow_self
  have hpow : (2:ℝ)^T ≤ 2^(d * BlockCount T (d/8)) :=
    pow_le_pow_right₀ (by norm_num) hTd
  rw [pow_mul] at hpow
  exact (by exact_mod_cast htwo : (T+1:ℝ) ≤ (2:ℝ)^T).trans hpow

lemma stopping_step_bound {d N K : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N) (hNK : N ≤ K)
    (T : ℕ) :
    (T+1:ℝ) * RealStep d N ^ BlockCount T (d/8) ≤
      ((2*StepConstant)^d * (K:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) := by
  have hSp := stepConstant_pos
  have hR := realStep_pos d hN
  have hn0 : (0:ℝ) ≤ N := by positivity
  have hroot : (N:ℝ)^(1/((d/8:ℕ):ℝ)) ≤ (K:ℝ)^(1/((d/8:ℕ):ℝ)) :=
    Real.rpow_le_rpow hn0 (by exact_mod_cast hNK) (by positivity)
  calc
    _ ≤ ((2:ℝ)^d)^BlockCount T (d/8) * RealStep d N ^ BlockCount T (d/8) :=
      mul_le_mul_of_nonneg_right (stopping_factor_bound hd T) (by positivity)
    _ = ((2*StepConstant)^d * (N:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) := by
      rw [← mul_pow]
      congr 1
      simp only [RealStep, mul_pow]
      ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hroot (by positivity)) _

lemma stopping_step_bound_three {d N K T : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    (hNK : N ≤ K) (hT : 0 < T) :
    3 * ((T+1:ℝ) * RealStep d N ^ BlockCount T (d/8)) ≤
      (SuccessConstant^d * (K:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) := by
  have hSp := stepConstant_pos
  have hR := realStep_pos d hN
  have hb := blockCount_pos hT (by omega : 0 < d/8)
  have h3 : (3:ℝ) ≤ ((3:ℝ)^d)^BlockCount T (d/8) := by
    rw [← pow_mul]
    have hdb : 1 ≤ d * BlockCount T (d/8) := Nat.mul_pos (by omega) hb
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hdb
  have hroot0 : 0 ≤ (K:ℝ)^(1/((d/8:ℕ):ℝ)) := by positivity
  calc
    _ ≤ ((3:ℝ)^d)^BlockCount T (d/8) *
        ((2*StepConstant)^d * (K:ℝ)^(1/((d/8:ℕ):ℝ))) ^ BlockCount T (d/8) :=
      mul_le_mul h3 (stopping_step_bound hd hN hNK T)
        (by positivity) (by positivity)
    _ = _ := by
      rw [← mul_pow]
      congr 1
      rw [← mul_assoc, ← mul_pow]
      congr 2
      dsimp [SuccessConstant]
      ring

lemma cap_constant_le {d : ℕ} (hd : 1 ≤ d) : (3*4^d:ℝ) ≤ 12^d := by
  have h3 : (3:ℝ) ≤ 3^d := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hd
  calc
    _ ≤ 3^d*4^d := mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

lemma terminal_angular_zero_bound {d : ℕ} (hd : 16 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    (3*4^d:ℝ)*ε^(d-1) ≤ 4^d*ε^(((d:ℝ)-1)/2) := by
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  have hα : (1:ℝ) ≤ ((d:ℝ)-1)/2 := by linarith
  have hεa : ε^(((d:ℝ)-1)/2) ≤ ε := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε (by linarith : ε ≤ 1) hα
  have hn : ((d-1:ℕ):ℝ) = (d:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have he : ε^(d-1) = ε^(((d:ℝ)-1)/2) * ε^(((d:ℝ)-1)/2) := by
    rw [← Real.rpow_add hε, ← Real.rpow_natCast, hn]
    congr 1
    ring
  rw [he]
  have haux : 3*ε^(((d:ℝ)-1)/2) ≤ 1 := by linarith
  calc
    _ = (4^d*ε^(((d:ℝ)-1)/2)) * (3*ε^(((d:ℝ)-1)/2)) := by ring
    _ ≤ (4^d*ε^(((d:ℝ)-1)/2)) * 1 := mul_le_mul_of_nonneg_left haux (by positivity)
    _ = _ := mul_one _

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelIntegral
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)
variable {X : Type*} [MeasurableSpace X]
variable (w : ℕ → State M → X → ℝ≥0∞) (ι : X → Vector d)

lemma measurable_records_at (s : X) (k : ℕ) :
    Measurable (fun A : Rows d k => ((s, (fun i => (A i,⟪ι s,A i⟫))) : X × Observations d k)) := by
  exact measurable_const.prodMk
    (Measurable.of_eval (fun index => (measurable_pi_apply index).prodMk (by fun_prop)))

lemma cont_eq_integral (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (n k : ℕ) (j : State M) (s : X) :
    K.cont w ι n k j s =
      ∫⁻ A : Rows d k, K.eval w n k j s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d k) := by
  classical
  induction k generalizing n j with
  | zero => simp [cont, eval, RowLaw]
  | succ k ih =>
    have hf : Measurable (fun A : Rows d (k+1) =>
        K.eval w n (k+1) j s (fun i => (A i,⟪ι s,A i⟫))) := by
      exact (K.measurable_eval w hK hw n (k+1) j).comp (measurable_records_at ι s (k+1))
    rw [RowLaw, NoiselessRegression.lintegral_pi_cons _ _ hf]
    unfold cont
    apply lintegral_congr
    intro x
    simp only [eval, Fin.cons_zero]
    have hm (a : Action M) : Measurable (fun A : Rows d k =>
        if a.1 then w (n+1) a.2 s
        else K.eval w (n+1) k a.2 s (fun i => (A i,⟪ι s,A i⟫))) := by
      rcases a with ⟨b,a⟩
      cases b
      · exact (K.measurable_eval w hK hw (n+1) k a).comp (measurable_records_at ι s k)
      · exact measurable_const
    change (∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a *
      if a.1 then w (n+1) a.2 s else K.cont w ι (n+1) k a.2 s) =
      ∫⁻ A : Rows d k, ∑ a : Action M, K.transition (n+1) j (x,⟪ι s,x⟫) a *
        if a.1 then w (n+1) a.2 s
        else K.eval w (n+1) k a.2 s (fun i => (A i,⟪ι s,A i⟫))
        ∂Measure.pi (fun _ => stdGaussian (Vector d))
    rw [lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [lintegral_const_mul _ (hm a)]
    congr 1
    rcases a with ⟨b,a⟩
    cases b
    · exact ih (n+1) a
    · simp

lemma pathValue_integral_le (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (s : X) :
    (∫⁻ A : Rows d T, K.pathValue w s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d T)) ≤
      ∑ a : Action M, K.initial a *
        (∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s) := by
  classical
  have hm (a : Action M) : Measurable (fun A : Rows d T =>
      if a.1 then w 0 a.2 s else K.eval w 0 T a.2 s (fun i => (A i,⟪ι s,A i⟫))) := by
    rcases a with ⟨b,a⟩
    cases b
    · exact (K.measurable_eval w hK hw 0 T a).comp (measurable_records_at ι s T)
    · exact measurable_const
  unfold pathValue
  rw [lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
  apply Finset.sum_le_sum
  intro a _
  rw [lintegral_const_mul _ (hm a)]
  apply mul_le_mul' le_rfl
  rcases a with ⟨b,a⟩
  cases b
  · change (∫⁻ A : Rows d T, K.eval w 0 T a s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d T)) ≤ _
    rw [← K.cont_eq_integral w ι hK hw 0 T a s]
    exact K.cont_le_forced_sum w ι hK 0 T a s
  · change (∫⁻ _A : Rows d T, w 0 a s ∂(RowLaw d T)) ≤ _
    rw [lintegral_const]
    have : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance
    simp only [measure_univ, mul_one]
    simpa only [MemoryPrecision.stochCont] using
      (Finset.single_le_sum (fun length _ =>
        (show (0:ℝ≥0∞) ≤ MemoryPrecision.stochCont K.marginal w ι 0 length a s from zero_le))
        (show 0 ∈ Finset.range (T+1) by simp) :
          MemoryPrecision.stochCont K.marginal w ι 0 0 a s ≤
            ∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a s)

lemma experiment_fixed_measurable (hK : K.Borel)
    {f : Sphere d × Sphere d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : Sphere d × Rows d T => K.pathValue (K.outputTest f) z.1 (records z.1 z.2)) := by
  apply Finset.measurable_sum _
  intro a _
  apply Measurable.const_mul
  rcases a with ⟨b,a⟩
  cases b
  · exact (K.measurable_eval (K.outputTest f) hK (K.outputTest_measurable hf) 0 T a).comp (by
      exact measurable_fst.prodMk (Measurable.of_eval (fun index => by
        change Measurable (fun z : Sphere d × Rows d T => (z.2 index,⟪z.1.val,z.2 index⟫))
        fun_prop)))
  · exact (K.outputTest_measurable hf 0 a).comp measurable_fst

lemma integral_pathValue_bound (hK : K.Borel) (hw : ∀ n j, Measurable (w n j))
    (hι : Measurable ι) (ν : Measure X) {B : ℝ≥0∞}
    (hb : ∀ (r : ℕ), r ≤ T → ∀ j,
      (∫⁻ s, MemoryPrecision.stochCont K.marginal w ι 0 r j s ∂ν) ≤ B) :
    (∫⁻ s, ∫⁻ A : Rows d T, K.pathValue w s (fun i => (A i,⟪ι s,A i⟫)) ∂(RowLaw d T) ∂ν) ≤
      (T+1:ℝ≥0∞) * B := by
  classical
  have hm (a : Action M) : Measurable (fun s =>
      ∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s) :=
    Finset.measurable_sum _ (fun r _ =>
      MemoryPrecision.measurable_stochCont (K.marginal_measurable hK) hw hι 0 r a.2)
  calc
    _ ≤ ∫⁻ s, ∑ a : Action M, K.initial a *
        (∑ r ∈ Finset.range (T+1), MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s) ∂ν :=
      lintegral_mono (K.pathValue_integral_le w ι hK hw)
    _ = ∑ a : Action M, K.initial a *
        (∑ r ∈ Finset.range (T+1), ∫⁻ s,
          MemoryPrecision.stochCont K.marginal w ι 0 r a.2 s ∂ν) := by
      rw [lintegral_finsetSum _ (fun a _ => (hm a).const_mul _)]
      apply Finset.sum_congr rfl
      intro a _
      rw [lintegral_const_mul _ (hm a), lintegral_finsetSum _ (fun r _ =>
        MemoryPrecision.measurable_stochCont (K.marginal_measurable hK) hw hι 0 r a.2)]
    _ ≤ ∑ a : Action M, K.initial a * ((T+1:ℝ≥0∞)*B) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑ _r ∈ Finset.range (T+1), B := Finset.sum_le_sum (fun r hr => hb r (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hr)) a.2)
        _ = _ := by simp [nsmul_eq_mul]
    _ = _ := by rw [← Finset.sum_mul, K.initial_sum, one_mul]
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelVersion
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)
private lemma measurable_versionCoordinates (hK : K.Completed) (t : ℕ) (j : State M) (a : Action M) :
    Measurable (fun obs => K.versionCoordinates hK t j obs a) :=
  (hK t j a).measurable_mk
private lemma versionCoordinates_ae (hK : K.Completed) (t : ℕ) (j : State M) :
    ∀ᵐ obs ∂ObservationReference d, ∀ a, K.versionCoordinates hK t j obs a = K.transition t j obs a := by
  apply ae_all_iff.mpr
  intro a
  exact (hK t j a).ae_eq_mk.symm

lemma version_borel (hK : K.Completed) : (K.version hK).Borel := by
  intro t j a
  exact Measurable.ite
    (measurableSet_eq_fun (Finset.measurable_sum _ (fun b _ =>
      K.measurable_versionCoordinates hK t j b)) measurable_const)
    (K.measurable_versionCoordinates hK t j a) measurable_const

lemma version_transition_ae (hK : K.Completed) (t : ℕ) (j : State M) :
    ∀ᵐ obs ∂ObservationReference d, ∀ a, (K.version hK).transition t j obs a = K.transition t j obs a := by
  filter_upwards [K.versionCoordinates_ae hK t j] with obs h
  have he : ∑ a, K.versionCoordinates hK t j obs a = 1 := by
    simpa only [h] using K.transition_sum t j obs
  intro a
  simp only [version, h, K.transition_sum, ite_true]

lemma eval_eq_of_rules {L : Policy d M T} {X : Type*}
    (w : ℕ → State M → X → ℝ≥0∞) (n k : ℕ) (j : State M) (s : X)
    (obs : Observations d k)
    (h : ∀ t j i a, K.transition t j (obs i) a = L.transition t j (obs i) a) :
    K.eval w n k j s obs = L.eval w n k j s obs := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    simp only [eval, h]
    congr 1
    funext a
    congr 1
    split
    · rfl
    · exact ih (n+1) a.2 (Fin.tail obs) (fun t j i a => h t j i.succ a)

lemma version_pathValue_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hK : K.Completed) (s : X → Sphere d) (obs : X → Observations d T)
    (ho : ∀ i : Fin T, Measure.QuasiMeasurePreserving (fun z => obs z i) μ (ObservationReference d))
    (f : Sphere d × Sphere d → ℝ≥0∞) :
    (fun z => (K.version hK).pathValue ((K.version hK).outputTest f) (s z) (obs z)) =ᵐ[μ]
      (fun z => K.pathValue (K.outputTest f) (s z) (obs z)) := by
  have hall : ∀ᵐ z ∂μ, ∀ i t j a,
      (K.version hK).transition t j (obs z i) a = K.transition t j (obs z i) a := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro t
    apply ae_all_iff.mpr
    intro j
    exact (ho i).ae (K.version_transition_ae hK t j)
  filter_upwards [hall] with z hz
  change (∑ a : Action M, K.initial a * if a.1 then K.outputTest f 0 a.2 (s z)
    else (K.version hK).eval (K.outputTest f) 0 T a.2 (s z) (obs z)) = _
  simp only [pathValue]
  congr 1
  funext a
  congr 1
  split
  · rfl
  · exact (K.version hK).eval_eq_of_rules (K.outputTest f) 0 T a.2 (s z) (obs z)
      (fun t j i a => hz i t j a)
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_SeedAverage
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereUniformSphereOfNeZeroNat _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureRowsRowLaw _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel

lemma seed_average_bound {X Y : Type*} {Ω : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Ω] (π : Measure X) [SFinite π] (ν : Measure Y) [SFinite ν]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {f : X × (Ω × Y) → ℝ≥0∞}
    (hf : AEMeasurable f (π.prod (ρ.prod ν))) {B : ℝ≥0∞}
    (hb : ∀ᵐ ω ∂ρ, (∫⁻ z : X × Y, f (z.1,(ω,z.2)) ∂π.prod ν) ≤ B) :
    (∫⁻ z, f z ∂π.prod (ρ.prod ν)) ≤ B := by
  have hp := ((MeasurePreserving.id π).prod
      (Measure.measurePreserving_swap (μ := ν) (ν := ρ))).comp
    (measurePreserving_prodAssoc π ν ρ)
  let g : (X × Y) × Ω → ℝ≥0∞ := fun z => f (z.1.1,(z.2,z.1.2))
  have hg : AEMeasurable g ((π.prod ν).prod ρ) :=
    hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have he : (∫⁻ z, g z ∂(π.prod ν).prod ρ) = ∫⁻ z, f z ∂π.prod (ρ.prod ν) := by
    rw [← hp.map_eq]
    exact (lintegral_map' (by simpa only [hp.map_eq] using hf) hp.measurable.aemeasurable).symm
  rw [← he, lintegral_prod_symm _ hg]
  exact (lintegral_mono_ae hb).trans_eq (by simp)

namespace Policy
variable {d M T : ℕ}
lemma success_le_one {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    (ε : ℝ) : Success L ρ π ε ≤ 1 := by
  have : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance
  unfold Success experiment
  calc
    _ ≤ ∫⁻ _z : Sphere d × (Ω × Rows d T), (1 : ℝ≥0∞) ∂π.prod (ρ.prod (RowLaw d T)) :=
      lintegral_mono (fun z => (L z.2.1).pathValue_le_one _
        ((L z.2.1).outputTest_le_one (angleTest_le_one ε)) z.1 (records z.1 z.2.2))
    _ = 1 := by simp
lemma chordSuccess_le_one {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (π : Measure (Sphere d)) [IsProbabilityMeasure π]
    (ε : ℝ) : ChordSuccess L ρ π ε ≤ 1 := by
  have : IsProbabilityMeasure (RowLaw d T) := by unfold RowLaw; infer_instance
  unfold ChordSuccess experiment
  calc
    _ ≤ ∫⁻ _z : Sphere d × (Ω × Rows d T), (1 : ℝ≥0∞) ∂π.prod (ρ.prod (RowLaw d T)) :=
      lintegral_mono (fun z => (L z.2.1).pathValue_le_one _
        ((L z.2.1).outputTest_le_one (chordTest_le_one ε)) z.1 (records z.1 z.2.2))
    _ = 1 := by simp
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_StochasticMass
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
lemma stoch_sphere_mass {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N → ℝ≥0∞}
    {w : ℕ → Fin N → Sphere d → ℝ≥0∞}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (hδ1 : ∀ n j obs, ∑ a, δ n j obs a ≤ 1) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1) {H α : ℝ} (hH : 0 < H)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2)
    (hlocal : ∀ n j, SphereBallBound (w n j) H α)
    (b k : ℕ) (hk : k ≤ b*(d/8)) (n : ℕ) (j : Fin N) :
    SphereBallBound (stochCont δ w Subtype.val n k j)
      (H * RealStep d N ^ b) α := by
  have hp : 0 < d/8 := by omega
  have hK := realStep_one d hN
  have hK0 := realStep_pos d hN
  induction b generalizing k n j with
  | zero =>
    have : k = 0 := by omega
    subst k
    simpa [stochCont] using hlocal n j
  | succ b ih =>
    by_cases hk0 : k = 0
    · subst k
      apply (hlocal n j).mono
      simpa [stochCont] using le_mul_of_one_le_right hH.le (one_le_pow₀ hK)
    · let m := min k (d/8)
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmp : m ≤ d/8 := min_le_right _ _
      have hmk : m ≤ k := min_le_left _ _
      have hk' : k-m ≤ b*(d/8) := by
        dsimp [m]
        rw [Nat.succ_mul] at hk
        omega
      have hb := (Classical.choose_spec coefficient_step).2 d m N hd hm hmp hN α
        (H * RealStep d N ^ b) hαlo hαhi (mul_pos hH (pow_pos hK0 b))
        (fun a => stochCont δ w Subtype.val (n+m) (k-m) a)
        (fun a => measurable_stochCont hδ hw measurable_subtype_coe _ _ a)
        (fun a s => stochCont_le_one Subtype.val hδ1 hw1 _ _ a s)
        (fun a => ih (k-m) hk' (n+m) a)
        (fun a x => stochRoute δ n m j x a)
        (fun a => measurable_stochRoute hδ n m j a)
        (fun x => stochRoute_sum_le_one hδ1 n m j x)
      have he : stochCont δ w Subtype.val n k j =
          SphereBlock (fun a => stochCont δ w Subtype.val (n+m) (k-m) a)
            (fun a x => stochRoute δ n m j x a) := by
        funext s
        simpa [Nat.add_sub_of_le hmk, SphereBlock, WeightedBlock] using
          stochCont_unroll Subtype.val hδ n m (k-m) j s
      rw [he]
      convert hb using 1
      change H * RealStep d N ^ (b+1) = RealStep d N * (H * RealStep d N ^ b)
      rw [pow_succ]; ring

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma borel_sphere_bound (hK : K.Borel) (hd : 16 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    (∫⁻ z : MemoryPrecision.Kernel.Sphere d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) z.1 (records z.1 z.2)
      ∂(UniformSphere d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal
        ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)*RealStep d (2^M)^_root_.OAI.MemoryPrecision.BlockCount T (d/8)) := by
  have : NeZero d := ⟨by omega⟩
  rw [lintegral_prod _ (K.experiment_fixed_measurable hK (measurable_chordTest ε)).aemeasurable]
  apply K.integral_pathValue_bound (K.outputTest (chordTest ε)) Subtype.val hK
    (K.outputTest_measurable (measurable_chordTest ε)) measurable_subtype_coe (UniformSphere d)
  intro r hr j
  have hd' : (16:ℝ) ≤ d := by exact_mod_cast hd
  have hb := stoch_sphere_mass hd (show 1 ≤ 2^M from one_le_pow₀ (by norm_num))
    (K.marginal_measurable hK) (fun n j obs => (K.marginal_sum n j obs).le)
    (K.outputTest_measurable (measurable_chordTest ε))
    (K.outputTest_le_one (chordTest_le_one ε))
    (H := (3*4^d)*ε^((d:ℝ)-1-α)) (by positivity) hαlo hαhi
    (K.output_chord_sphere_local (by omega) hε (by linarith) (by linarith))
    (_root_.OAI.MemoryPrecision.BlockCount T (d/8)) r (hr.trans (blockCount_mul_ge T (by omega))) 0 j
  exact sphere_mass_bound hb

lemma completed_sphere_bound (hK : K.Completed) (hd : 16 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    (∫⁻ z : MemoryPrecision.Kernel.Sphere d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) z.1 (records z.1 z.2)
      ∂(UniformSphere d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal
        ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)*RealStep d (2^M)^_root_.OAI.MemoryPrecision.BlockCount T (d/8)) := by
  have : NeZero d := ⟨by omega⟩
  have he := K.version_pathValue_ae ((UniformSphere d).prod (RowLaw d T)) hK Prod.fst
    (fun z : MemoryPrecision.Kernel.Sphere d × Rows d T => records z.1 z.2)
    (fun i => show Measure.QuasiMeasurePreserving _ _ _ from
      sphere_sample_observation_quasi (by simpa using (show 3 ≤ d by omega)) i) (chordTest ε)
  rw [← lintegral_congr_ae he]
  exact (K.version hK).borel_sphere_bound (K.version_borel hK) hd hε hαlo hαhi

lemma chord_real_bound {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (hL : Admissible L ρ (UniformSphere d))
    (hd : 16 ≤ d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    ChordSuccess L ρ (UniformSphere d) ε ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal
        ((3*4^d:ℝ)*ε^((d:ℝ)-1-α)*RealStep d (2^M)^_root_.OAI.MemoryPrecision.BlockCount T (d/8)) := by
  have : NeZero d := ⟨by omega⟩
  apply seed_average_bound (UniformSphere d) (RowLaw d T) ρ
    (hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε))
  filter_upwards [hL.completed] with ω hω
  exact (L ω).completed_sphere_bound hω hd hε hαlo hαhi

lemma zero_fixed_sphere_bound {d M : ℕ} (K : Policy d M 0) (hd : 1 ≤ d)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : MemoryPrecision.Kernel.Sphere d × Rows d 0,
      K.pathValue (K.outputTest (chordTest ε)) z.1 (records z.1 z.2)
      ∂(UniformSphere d).prod (RowLaw d 0)) ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  have : NeZero d := ⟨by omega⟩
  have he (s : MemoryPrecision.Kernel.Sphere d) (obs : Observations d 0) :
      K.pathValue (K.outputTest (chordTest ε)) s obs =
        ∑ a : Action M, K.initial a * K.outputTest (chordTest ε) 0 a.2 s := by
    unfold pathValue
    simp only [eval, ite_self]
  simp_rw [he]
  have hm : Measurable (fun s : MemoryPrecision.Kernel.Sphere d =>
      ∑ a : Action M, K.initial a * K.outputTest (chordTest ε) 0 a.2 s) :=
    Finset.measurable_sum _ (fun a _ => (K.outputTest_measurable (measurable_chordTest ε) 0 a.2).const_mul _)
  have hm' : Measurable (fun z : MemoryPrecision.Kernel.Sphere d × Rows d 0 =>
      ∑ a : Action M, K.initial a * K.outputTest (chordTest ε) 0 a.2 z.1) :=
    hm.comp measurable_fst
  rw [lintegral_prod _ hm'.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_finsetSum _ (fun a _ =>
    (K.outputTest_measurable (measurable_chordTest ε) 0 a.2).const_mul _)]
  calc
    _ = ∑ a : Action M, K.initial a *
        (∫⁻ s, K.outputTest (chordTest ε) 0 a.2 s ∂UniformSphere d) := by
      apply Finset.sum_congr rfl
      intro a _
      exact lintegral_const_mul _ (K.outputTest_measurable (measurable_chordTest ε) 0 a.2)
    _ ≤ ∑ a : Action M, K.initial a * ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul' le_rfl (K.output_chord_sphere_total hd hε 0 a.2))
    _ = _ := by rw [← Finset.sum_mul, K.initial_sum, one_mul]

lemma chord_zero_bound {d M : ℕ} {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M 0)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (hL : Admissible L ρ (UniformSphere d))
    (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal ((3*4^d:ℝ)*ε^(d-1)) := by
  have : NeZero d := ⟨by omega⟩
  apply seed_average_bound (UniformSphere d) (RowLaw d 0) ρ
    (hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε))
  exact Filter.Eventually.of_forall (fun ω => (L ω).zero_fixed_sphere_bound hd hε)
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelEllipsoid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision Policy

lemma chord_real_coefficient {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : Admissible L ρ (UniformSphere d)) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal
      ((T+1:ℝ) * ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M)^_root_.OAI.MemoryPrecision.BlockCount T (d/8))) := by
  apply (Policy.chord_real_bound L ρ hL hd hε hαlo hαhi).trans_eq
  rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ T+1)]
  congr 1
  simp [ENNReal.ofReal_add]

lemma chord_half_sphere_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : Admissible L ρ (UniformSphere d)) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal
      (4^d * ε^(((d:ℝ)-1)/2) *
        (SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^_root_.OAI.MemoryPrecision.BlockCount T (d/8)) := by
  by_cases hT : T = 0
  · subst T
    simp only [blockCount_zero, pow_zero, mul_one]
    exact (Policy.chord_zero_bound L ρ hL (by omega) hε).trans
      (ENNReal.ofReal_le_ofReal (terminal_angular_zero_bound hd hε hε1))
  · have hb := chord_real_coefficient L ρ hL hd hε (le_refl (((d:ℝ)-1)/2)) (by linarith)
    have he : (d:ℝ)-1-((d:ℝ)-1)/2 = ((d:ℝ)-1)/2 := by ring
    rw [he] at hb
    apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hN : 1 ≤ 2^M := one_le_pow₀ (by norm_num)
    have hNK : 2^M ≤ (d/8+2)*2^M := by
      simp
    have hs := stopping_step_bound_three hd hN hNK (by omega : 0 < T)
    calc
      _ = (4^d * ε^(((d:ℝ)-1)/2)) * (3*((T+1:ℝ)*RealStep d (2^M)^_root_.OAI.MemoryPrecision.BlockCount T (d/8))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

lemma chord_half_ambient_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : Admissible L ρ (UniformSphere d)) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ChordSuccess L ρ (UniformSphere d) ε ≤ ENNReal.ofReal
      (12^d * ε^((d:ℝ)/2-1) *
        (SuccessConstant^d * (((2*(d/8)+4)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^_root_.OAI.MemoryPrecision.BlockCount T (d/8)) := by
  have hb := chord_real_coefficient L ρ hL hd hε (by linarith : ((d:ℝ)-1)/2 ≤ (d:ℝ)/2) le_rfl
  have he : (d:ℝ)-1-(d:ℝ)/2 = (d:ℝ)/2-1 := by ring
  rw [he] at hb
  apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hN : 1 ≤ 2^M := one_le_pow₀ (by norm_num)
  have hNK : 2^M ≤ (2*(d/8)+4)*2^M := by
    simp
  have hR := realStep_pos d hN
  have hs := stopping_step_bound hd hN hNK T
  have hSp := stepConstant_pos
  have hK : 2*StepConstant ≤ SuccessConstant := by dsimp [SuccessConstant]; linarith
  have hroot : 0 ≤ (((2*(d/8)+4)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) := by positivity
  have hbase := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ 2*StepConstant) hK d) hroot
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2*StepConstant)^d *
    (((2*(d/8)+4)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ))) hbase (_root_.OAI.MemoryPrecision.BlockCount T (d/8))
  calc
    _ = ((3*4^d:ℝ)*ε^((d:ℝ)/2-1))*((T+1:ℝ)*RealStep d (2^M)^_root_.OAI.MemoryPrecision.BlockCount T (d/8)) := by ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_right (cap_constant_le (by omega : 1 ≤ d)) (by positivity))
      (hs.trans hpow) (by positivity) (by positivity)

end MemoryPrecision.Kernel

namespace MemoryPrecision.Kernel
open Policy

theorem source_ellipsoid_success : SourceEllipsoidStatement := by
  refine ⟨MemoryPrecision.SuccessConstant, 12, MemoryPrecision.successConstant_one, by norm_num, ?_⟩
  intro d M T hd ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine ⟨le_min (Policy.success_le_one L ρ (UniformSphere d) ε) ?_,
    le_min (Policy.chordSuccess_le_one L ρ (UniformSphere d) ε) ?_, ?_⟩
  · exact (Policy.success_le_chord L ρ (UniformSphere d) ε).trans
      (chord_half_sphere_bound L ρ hL hd hε hε1)
  · exact chord_half_ambient_bound L ρ hL hd hε
  · intro x hx
    exact (NoiselessRegression.chord_le_arccos x.2 x.1).trans hx
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_StreamArithmetic
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma streamConstant_pos : 0 < StreamConstant := by
  have h := successConstant_one
  dsimp [StreamConstant]
  linarith

lemma blockCount_antitone {p q : ℕ} (hq : 0 < q) (hqp : q ≤ p) (T : ℕ) :
    BlockCount T p ≤ BlockCount T q := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hq) (by exact_mod_cast hqp)

lemma power_le_exp {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : x^d ≤ Real.exp (x*d) := by
  have hl : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h := pow_le_pow_left₀ hx hl d
  simpa only [← Real.rpow_natCast, ← Real.exp_mul] using h

lemma stream_root_exp {d M : ℕ} (hd : 32 ≤ d) :
    (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) ≤ Real.exp ((d:ℝ)+16*M/d) := by
  have hn : (d/8+2)*2^M ≤ 2^(d+M) := by
    have h : d/8+2 ≤ 2^d := (show d/8+2 ≤ d+1 by omega).trans Nat.lt_two_pow_self
    simpa [pow_add] using Nat.mul_le_mul_right (2^M) h
  have ht : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hnum : (((d/8+2)*2^M:ℕ):ℝ) ≤ Real.exp ((d:ℝ)+M) := by
    calc
      _ ≤ (2:ℝ)^(d+M) := by exact_mod_cast hn
      _ ≤ (Real.exp 1)^(d+M) := pow_le_pow_left₀ (by norm_num) ht _
      _ = _ := by rw [← Real.rpow_natCast, ← Real.exp_mul]; simp
  have hdp : (d:ℝ)/16 ≤ (d/8:ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 16)).2
    exact_mod_cast (show d ≤ (d/8)*16 by omega)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hr : ((d:ℝ)+M)/((d/8:ℕ):ℝ) ≤ (d:ℝ)+16*M/d := by
    calc
      _ ≤ ((d:ℝ)+M)/((d:ℝ)/16) := div_le_div_of_nonneg_left (by positivity) (by positivity) hdp
      _ = 16+16*M/d := by field_simp
      _ ≤ _ := by
        have : (16:ℝ) ≤ d := by exact_mod_cast (show 16 ≤ d by omega)
        linarith
  calc
    _ ≤ (Real.exp ((d:ℝ)+M))^(1/((d/8:ℕ):ℝ)) :=
      Real.rpow_le_rpow (by positivity) hnum (by positivity)
    _ = Real.exp (((d:ℝ)+M)/((d/8:ℕ):ℝ)) := by rw [← Real.exp_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hr

lemma stream_step_exp {d M : ℕ} (hd : 32 ≤ d) :
    SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) ≤
      Real.exp ((d:ℝ)*(SuccessConstant+1)+16*M/d) := by
  have hS := successConstant_one
  calc
    _ ≤ Real.exp (SuccessConstant*d) * Real.exp ((d:ℝ)+16*M/d) :=
      mul_le_mul (power_le_exp (by linarith) d) (stream_root_exp hd) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma stream_step_one (d M : ℕ) :
    1 ≤ SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)) := by
  apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ successConstant_one)
  apply Real.one_le_rpow _ (by positivity)
  exact_mod_cast (show 1 ≤ (d/8+2)*2^M by
    exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by positivity)))

lemma stream_exponent_bound {d M : ℕ} (hd : 32 ≤ d) :
    (d:ℝ)*(SuccessConstant+5)+16*M/d ≤
      (((d:ℝ)-1)/2)*StreamConstant*(1+(M:ℝ)/(d:ℝ)^2) := by
  have hS := successConstant_one
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (d:ℝ)/3 ≤ ((d:ℝ)-1)/2 := by
    have : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc : 0 ≤ StreamConstant := streamConstant_pos.le
  calc
    _ ≤ (SuccessConstant+21)*(d:ℝ)+(SuccessConstant+21)*(M/d) := by
      have hM : 0 ≤ (M:ℝ)/d := by positivity
      have hm := mul_le_mul_of_nonneg_right (show (16:ℝ) ≤ SuccessConstant+21 by linarith) hM
      have hn : (d:ℝ)*(SuccessConstant+5) ≤ (SuccessConstant+21)*(d:ℝ) := by nlinarith
      simpa only [mul_div_assoc] using add_le_add hn hm
    _ = (d:ℝ)/3*StreamConstant*(1+(M:ℝ)/(d:ℝ)^2) := by
      dsimp [StreamConstant]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd3 hc) (by positivity)

lemma stream_full_factor {d M T : ℕ} (hd : 32 ≤ d) (hT : 0 < T) :
    (4:ℝ)^d * (SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8) ≤
      Real.exp ((((d:ℝ)-1)/2)*StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)) := by
  let b := BlockCount T ((d-1)/8)
  let K := SuccessConstant^d * (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ))
  have hK : 1 ≤ K := stream_step_one d M
  have hb : 1 ≤ b := blockCount_pos hT (by omega)
  have hbp : BlockCount T (d/8) ≤ b := blockCount_antitone (by omega) (by omega) T
  have h4 : (4:ℝ)^d ≤ Real.exp (4*d*(b:ℝ)) := by
    apply (power_le_exp (by norm_num : (0:ℝ) ≤ 4) d).trans
    apply Real.exp_le_exp.mpr
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast hb)
  have hpow : K^b ≤ Real.exp (((d:ℝ)*(SuccessConstant+1)+16*M/d)*(b:ℝ)) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ K) (stream_step_exp hd) b
    simpa only [← Real.rpow_natCast, ← Real.exp_mul, K] using h
  calc
    _ ≤ (4:ℝ)^d * K^b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK hbp) (by positivity)
    _ ≤ Real.exp (4*d*(b:ℝ)) * Real.exp (((d:ℝ)*(SuccessConstant+1)+16*M/d)*(b:ℝ)) :=
      mul_le_mul h4 hpow (by positivity) (by positivity)
    _ = Real.exp (((d:ℝ)*(SuccessConstant+5)+16*M/d)*(b:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (stream_exponent_bound hd) (by positivity))

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_StreamZero
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision

lemma zero_cap_coefficient {d : ℕ} (hd : 32 ≤ d) :
    (3*4^d:ℝ) ≤ (20:ℝ)^(((d:ℝ)-1)/2) := by
  have hs : (9:ℝ)*16^d ≤ 20^(d-1) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
    have he : 32+k-1 = 31+k := by omega
    rw [he, pow_add, pow_add]
    have hb : (9:ℝ)*16^32 ≤ 20^31 := by norm_num
    calc
      _ = ((9:ℝ)*16^32)*16^k := by ring
      _ ≤ 20^31*20^k := mul_le_mul hb (pow_le_pow_left₀ (by norm_num) (by norm_num : (16:ℝ) ≤ 20) k)
        (by positivity) (by positivity)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hl : (3*4^d:ℝ)^2 = 9*16^d := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  have hr : ((20:ℝ)^(((d:ℝ)-1)/2))^2 = 20^(d-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 20)]
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rwa [hl,hr]

lemma zero_cap_precise {d : ℕ} (hd : 32 ≤ d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1/10) :
    (3*4^d:ℝ)*ε^(d-1) ≤ (2*ε)^(((d:ℝ)-1)/2) := by
  let a := ((d:ℝ)-1)/2
  have ha : 0 ≤ a := by
    dsimp [a]
    have : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he : ε^(d-1) = ε^a*ε^a := by
    rw [← Real.rpow_add hε, ← Real.rpow_natCast]
    congr 1
    dsimp [a]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hsmall : (10*ε)^a ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) ha
  calc
    _ ≤ (20:ℝ)^a * ε^(d-1) := mul_le_mul_of_nonneg_right (zero_cap_coefficient hd) (by positivity)
    _ = (2*ε)^a*(10*ε)^a := by
      rw [he, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hε.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) hε.le]
      have h20 := Real.mul_rpow (z := a) (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) ≤ 10)
      norm_num only [show (2:ℝ)*10=20 by norm_num] at h20
      rw [h20]
      ring
    _ ≤ (2*ε)^a * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := mul_one _
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision Policy

lemma source_stream_explicit :
  ∀ d M T : ℕ, 32 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
  ∀ L : Ω → Policy d M T, Admissible L ρ (UniformSphere d) →
    Success L ρ (UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
      ((2*ε*Real.exp (StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2))) := by
  intro d M T hd ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine le_min (Policy.success_le_one L ρ (UniformSphere d) ε) ?_
  apply (Policy.success_le_chord L ρ (UniformSphere d) ε).trans
  by_cases hT : T = 0
  · subst T
    simp only [BlockCount, Nat.ceil_zero, zero_div, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    exact (Policy.chord_zero_bound L ρ hL (by omega) hε).trans
      (ENNReal.ofReal_le_ofReal (zero_cap_precise hd hε hε1))
  · apply (chord_half_sphere_bound L ρ hL (by omega) hε hε1).trans
    apply ENNReal.ofReal_le_ofReal
    let a := ((d:ℝ)-1)/2
    let X := StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)
    have ha : 0 ≤ a := by
      dsimp [a]
      have : (32:ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have he : Real.exp (a*X) = (Real.exp X)^a := by rw [← Real.exp_mul, mul_comm]
    have h2 : ε^a ≤ (2*ε)^a := Real.rpow_le_rpow hε.le (by linarith) ha
    calc
      _ = ε^a * ((4:ℝ)^d * (SuccessConstant^d *
        (((d/8+2)*2^M:ℕ):ℝ)^(1/((d/8:ℕ):ℝ)))^BlockCount T (d/8)) := by dsimp [a, BlockCount, MemoryPrecision.BlockCount]; ring
      _ ≤ ε^a * Real.exp (a*X) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [a, X, BlockCount, MemoryPrecision.BlockCount, mul_assoc] using stream_full_factor hd (by omega : 0 < T)
      _ ≤ (2*ε)^a * Real.exp (a*X) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (2*ε*Real.exp X)^a := by
        rw [he]
        exact (Real.mul_rpow (by positivity : (0:ℝ) ≤ 2*ε) (Real.exp_pos X).le).symm
theorem source_stream_success : SourceStreamStatement :=
  ⟨StreamConstant, streamConstant_pos, 32, by norm_num, source_stream_explicit⟩
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_PointwiseMain
attribute [-instance] _root_.OAI.MemoryPrecision.instIsProbabilityMeasureSpaceCubeAmbient _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

theorem pointwise_density : PointwiseDensityStatement := by
  intro d m p hd hm hmd hp β H R hgap hH hR z μ hμ hs hb hac
  let : IsFiniteMeasure μ := hμ
  obtain ⟨F,hFm,hF0,hden,hFs,hFnorm⟩ :=
    exact_finite_density d m p hp hm β H R hgap hH hR z μ hs hb
  have he := pointwiseDensity_ae_eq hm μ F hFm hF0 hden
  refine ⟨?_, PointwiseDensity_nonneg μ m, measurable_PointwiseDensity μ m,
    ?_, ?_, pointwiseDensity_ae_eq hm μ, ?_⟩
  · intro δ hδ
    exact ⟨fun r hr => radialMixture_nonneg m δ hr, radialMixture_measurable m δ,
      radialMixture_integral m hm hδ, radialMixture_tail m hm hδ⟩
  · intro A hA
    exact pointwiseDensity_fullRank hd hm hmd μ hac A hA
  · exact (withDensity_congr_ae (he.fun_comp ENNReal.ofReal)).trans hden
  · have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hpE : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hpow := ENNReal.rpow_le_rpow hFnorm (show 0 ≤ (p:ℝ) by positivity)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpE (by finiteness)] at hpow
    simp only [ENNReal.toReal_natCast] at hpow
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0, ENNReal.rpow_one] at hpow
    simp only [ENNReal.rpow_natCast] at hpow
    have hi : (fun x => ENNReal.ofReal (PointwiseDensity μ m x)^p) =ᵐ[MatrixLabelReference d m]
        (fun x => ‖F x‖ₑ^p) := by
      filter_upwards [he] with x hx
      rw [hx, Real.enorm_eq_ofReal (hF0 x)]
    rw [lintegral_congr_ae hi]
    exact hpow
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u
namespace MemoryPrecision

open MeasureTheory
open scoped ENNReal

theorem main_oai :
  AmbientGramStatement ∧
  FiniteDensityStatement ∧
  MeasurableTestStatement ∧
  JointL1Statement ∧
  PointwiseDensityStatement ∧
  CoefficientStepStatement ∧
  Kernel.SourceEllipsoidStatement.{u} ∧
  CubeBlockStatement ∧
  (∃ D : ℝ, Real.exp 1 ≤ D ∧ ∃ d₀ : ℕ, ∃ hd₀ : 16 ≤ d₀, ∃ c : ℝ, 0 < c ∧
    ∀ d M T : ℕ, ∀ hd : d₀ ≤ d, M ≤ d^2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ K : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.ModelAdmissible.{u} K ρ →
      MemoryPrecision.Kernel.Policy.Success K ρ
        (MemoryPrecision.Kernel.CubePrior (MemoryPrecision.Kernel.cubePrior_dimension hd₀ hd)) ε ≤
          min 1 (ENNReal.ofReal
            (D^((d/2)*(MemoryPrecision.Kernel.BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ))) ∧
      ((∀ signal : MemoryPrecision.Kernel.Sphere d,
        (@OfNat.ofNat ℝ≥0∞ 2
          (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) /
        (@OfNat.ofNat ℝ≥0∞ 3
          (@instOfNatAtLeastTwo ℝ≥0∞ 3 ENNReal.instAddCommMonoidWithOne.toNatCast inferInstance)) ≤
          (∫⁻ observation,
            MemoryPrecision.Kernel.Policy.experiment K
              (MemoryPrecision.Kernel.Policy.angleTest ε) (signal, observation)
            ∂ρ.prod (MemoryPrecision.Kernel.RowLaw d T))) →
        c*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ))) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, 0 < d₀ ∧
    ∀ d M T : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Ω → MemoryPrecision.Kernel.Policy d M T,
      MemoryPrecision.Kernel.Policy.Admissible L ρ (MemoryPrecision.Kernel.UniformSphere d) →
      MemoryPrecision.Kernel.Policy.Success L ρ (MemoryPrecision.Kernel.UniformSphere d) ε ≤ min 1 (ENNReal.ofReal
        ((2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(MemoryPrecision.Kernel.BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)))) :=
  ⟨ambient_gram, finite_density, measurable_test, joint_l1, pointwise_density, coefficient_step, Kernel.source_ellipsoid_success, cube_block, Kernel.source_cube_success, Kernel.source_stream_success⟩

end MemoryPrecision

end OAI
end

theorem solution.{u} : type_of% @OAI.MemoryPrecision.main_oai.{u} := @OAI.MemoryPrecision.main_oai.{u}
