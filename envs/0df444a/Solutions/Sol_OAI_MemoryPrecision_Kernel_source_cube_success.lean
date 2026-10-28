-- Prove2me | solution 1 for OAI.MemoryPrecision.Kernel.source_cube_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T21:18:08.222987+00:00
-- url     : https://prove2.me/submissions/daf12fb9-4f68-49a0-bfd8-7f332f46d33c

import Mathlib
import Definitions.Def_MemoryPrecision
import Definitions.Def_OAIQ1Mp000

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

lemma unitBallLaw_isometry_apply (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    unitBallLaw (e ⁻¹' s) = unitBallLaw s := by
  have hb : e ⁻¹' Metric.closedBall (0 : E) 1 = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hset : e ⁻¹' s ∩ Metric.closedBall (0 : E) 1 =
      e ⁻¹' (s ∩ Metric.closedBall 0 1) := by rw [Set.preimage_inter, hb]
  rw [unitBallLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet, hset]
  congr 1
  calc
    _ = (Measure.map e volume) (s ∩ Metric.closedBall 0 1) :=
      (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
    _ = _ := by rw [e.measurePreserving.map_eq]

lemma ambientSphereLaw_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
  rw [ambientSphereLaw, Measure.map_apply (by fun_prop) hs,
    sphereLaw_apply (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x,hx⟩,hs,rfl⟩

lemma ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by
  refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply e.continuous.measurable hs,
    ambientSphereLaw_apply (e.continuous.measurable hs), ambientSphereLaw_apply hs]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      refine ⟨r,hr,e y,⟨?_,hys⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hy
      · simpa only [map_smul] using congrArg e he
    · rintro ⟨r,hr,y,⟨hy,hys⟩,he⟩
      refine ⟨r,hr,e.symm y,⟨?_,?_⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using hy
      · simpa using hys
      · simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm he
  rw [hset, unitBallLaw_isometry_apply]

lemma ambientSphereLaw_ae_norm [Nontrivial E] :
    ∀ᵐ x : E ∂ambientSphereLaw, ‖x‖ = 1 := by
  filter_upwards [Measure.support_mem_ae (μ := ambientSphereLaw (E := E))] with x hx
  exact mem_sphere_zero_iff_norm.mp (ambientSphereLaw_support hx)

lemma sphere_inner_sq_integrable [Nontrivial E] (v : E) :
    Integrable (fun x => ⟪v,x⟫^2) (ambientSphereLaw (E := E)) := by
  apply (integrable_const (‖v‖^2)).mono' (by fun_prop)
  filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
  have h := abs_real_inner_le_norm v x
  rw [hx, mul_one] at h
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 h)

lemma sphere_inner_sq_eq [Nontrivial E] {v w : E} (h : ‖v‖ = ‖w‖) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = ∫ x, ⟪w,x⟫^2 ∂ambientSphereLaw := by
  let e := (ℝ ∙ (v-w))ᗮ.reflection
  have he : e v = w := Submodule.reflection_sub h
  have hi := (ambientSphereLaw_isometry e).integral_comp
    e.toMeasurableEquiv.measurableEmbedding (fun x => ⟪w,x⟫^2)
  rw [← he] at hi
  simp only [e.inner_map_map] at hi
  simpa only [he] using hi

lemma sphere_inner_sq_unit [Nontrivial E] {v : E} (hv : ‖v‖ = 1) :
    (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ x : E, (∑ i, ⟪b i,x⟫^2) = ‖x‖^2 := by
    intro x
    simpa only [real_inner_comm x, pow_two, real_inner_self_eq_norm_sq] using
      b.sum_inner_mul_inner x x
  have h : (Module.finrank ℝ E : ℝ) * (∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw) = 1 := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ E), ∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw := by
        have heq : ∀ i, (∫ x, ⟪b i,x⟫^2 ∂ambientSphereLaw) =
            ∫ x, ⟪v,x⟫^2 ∂ambientSphereLaw := fun i =>
          sphere_inner_sq_eq (by rw [b.norm_eq_one, hv])
        simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∫ x, ∑ i, ⟪b i,x⟫^2 ∂ambientSphereLaw :=
        (integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i))).symm
      _ = ∫ _ : E, (1 : ℝ) ∂ambientSphereLaw := by
        apply integral_congr_ae
        filter_upwards [ambientSphereLaw_ae_norm (E := E)] with x hx
        rw [hsum, hx, one_pow]
      _ = 1 := by simp
  have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne'
  exact (eq_div_iff hd).2 (by simpa only [mul_comm] using h)

lemma sphere_projection_sq_integrable [Nontrivial E] (U : Submodule ℝ E) :
    Integrable (fun x => ‖U.orthogonalProjectionOnto x‖^2) (ambientSphereLaw (E := E)) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  exact integrable_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))

lemma sphere_projection_sq_integral [Nontrivial E] (U : Submodule ℝ E) :
    (∫ x, ‖U.orthogonalProjectionOnto x‖^2 ∂ambientSphereLaw) =
      (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) := by
  let b := stdOrthonormalBasis ℝ U
  have hsum : ∀ x : E, (∑ i, ⟪(b i : E),x⟫^2) = ‖U.orthogonalProjectionOnto x‖^2 := by
    intro x
    have h := b.sum_inner_mul_inner (U.orthogonalProjectionOnto x) (U.orthogonalProjectionOnto x)
    rw [real_inner_self_eq_norm_sq] at h
    have hi : ∀ i, ⟪U.orthogonalProjectionOnto x, b i⟫ = ⟪b i, U.orthogonalProjectionOnto x⟫ :=
      fun i => real_inner_comm _ _
    simpa only [hi, U.inner_orthogonalProjectionOnto_eq_of_mem_left, pow_two] using h
  simp_rw [← hsum]
  rw [integral_finsetSum _ (fun i _ => sphere_inner_sq_integrable (b i : E))]
  have hi : ∀ i, (∫ x, ⟪(b i : E), x⟫^2 ∂ambientSphereLaw) =
      1 / (Module.finrank ℝ E : ℝ) := fun i =>
    sphere_inner_sq_unit (by exact b.norm_eq_one i)
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]

lemma sphereIsometry_preserving [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereIsometry e) (sphereLaw (E := E)) (sphereLaw (E := E)) := by
  refine ⟨(sphereIsometry e).continuous.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change (sphereLaw (E := E)).map (e ∘ Subtype.val) = ambientSphereLaw
  rw [← Measure.map_map e.continuous.measurable (by fun_prop)]
  exact (ambientSphereLaw_isometry e).map_eq

omit [MeasurableSpace E] [BorelSpace E] in
lemma reflection_dist (U : Submodule ℝ E) (x : E) :
    dist x (U.reflection x) = 2 * ‖Uᗮ.starProjection x‖ := by
  rw [dist_eq_norm, Submodule.reflection_apply]
  have heq : x - (2 • U.starProjection x - x) = (2 : ℝ) • Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal]
    simp only [sub_apply, ContinuousLinearMap.id_apply, two_smul ℝ]
    abel
  rw [heq, norm_smul]
  norm_num

lemma sphere_projection_large [Nontrivial E] (U : Submodule ℝ E)
    (hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ E) :
    sphereLaw {x : Metric.sphere (0 : E) 1 | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x.val‖^2} ≤
      ENNReal.ofReal (5/16 : ℝ) := by
  have hi := ofReal_integral_eq_lintegral_ofReal (sphere_projection_sq_integrable U)
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖U.orthogonalProjectionOnto x‖)
  rw [sphere_projection_sq_integral] at hi
  have hmark := meas_ge_le_lintegral_div
    (μ := ambientSphereLaw (E := E)) (f := fun x => ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2))
    (by fun_prop) (by norm_num : ENNReal.ofReal (4/5 : ℝ) ≠ 0) (ENNReal.ofReal_ne_top : ENNReal.ofReal (4/5 : ℝ) ≠ ∞)
  rw [← hi] at hmark
  have hset : {x : E | ENNReal.ofReal (4/5 : ℝ) ≤ ENNReal.ofReal (‖U.orthogonalProjectionOnto x‖^2)} =
      {x : E | (4/5 : ℝ) ≤ ‖U.orthogonalProjectionOnto x‖^2} := by
    ext x
    change ENNReal.ofReal (4/5 : ℝ) ≤ _ ↔ _
    exact ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)
  rw [hset, ambientSphereLaw,
    (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).map_apply] at hmark
  apply hmark.trans
  have hd : (0 : ℝ) < Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hdiv : (Module.finrank ℝ U : ℝ) / (Module.finrank ℝ E : ℝ) ≤ 1/4 := by
    rw [div_le_iff₀ hd]
    have : (4 : ℝ) * Module.finrank ℝ U ≤ Module.finrank ℝ E := by exact_mod_cast hU
    linarith
  calc
    _ ≤ ENNReal.ofReal (1/4 : ℝ) / ENNReal.ofReal (4/5 : ℝ) := by gcongr
    _ = ENNReal.ofReal (5/16 : ℝ) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4/5)]
      norm_num

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
-- module Solutions.OAIQ1_Mem.GaussianRegression_Rotational
attribute [-instance] _root_.OAI.ProjectionMoments.realMatrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fubini bounds and rotational lower bounds for sequential estimation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
lemma ae_fiber_aemeasurable {f : X × Y → Z} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x,y)) μ := by
  have he := Measure.ae_ae_of_ae_prod hf.prod_swap.ae_eq_mk
  filter_upwards [he] with y hy
  have hm : Measurable (fun x => hf.prod_swap.mk _ (y,x)) :=
    hf.prod_swap.measurable_mk.comp (measurable_const.prodMk measurable_id)
  exact hm.aemeasurable.congr (Filter.EventuallyEq.symm hy)

end FubiniAux

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
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeCaps
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

lemma coordinate_ball_root_volume (n : ℕ) :
    volume (coordinateBall n (Real.sqrt n)) ≤ ENNReal.ofReal ((12:ℝ)^n) := by
  have hpoint (x : Fin n → ℝ) :
      (coordinateBall n (Real.sqrt n)).indicator (fun _ => (1:ℝ≥0∞)) x ≤
        ENNReal.ofReal (Real.exp n) * ∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/4)) := by
    by_cases hx : x ∈ coordinateBall n (Real.sqrt n)
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_sum, ← Real.exp_add]
      have hs : (∑ i, (x i)^2) ≤ n := by
        have hp := pow_le_pow_left₀ (norm_nonneg _) hx 2
        change coordinateNorm x ^ 2 ≤ (Real.sqrt (n:ℝ)) ^ 2 at hp
        rw [coordinateNorm_sq, Real.sq_sqrt (by positivity)] at hp
        exact hp
      have he : 1 ≤ Real.exp ((n:ℝ) + ∑ i, -(x i)^2/4) := by
        apply Real.one_le_exp_iff.mpr
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      exact_mod_cast (ENNReal.ofReal_le_ofReal he)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc
    volume (coordinateBall n (Real.sqrt n)) =
        ∫⁻ x : Fin n → ℝ, (coordinateBall n (Real.sqrt n)).indicator (fun _ => (1:ℝ≥0∞)) x := by
      rw [lintegral_indicator_const (measurableSet_coordinateBall _ _), one_mul]
    _ ≤ ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (Real.exp n) *
        ∏ i, ENNReal.ofReal (Real.exp (-(x i)^2/4)) := lintegral_mono hpoint
    _ = ENNReal.ofReal (Real.exp n) *
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z^2)/4)))^n := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume n (fun _ => fun z : ℝ => ENNReal.ofReal (Real.exp (-(z^2)/4))) (fun _ => by fun_prop)]
      simp
    _ ≤ ENNReal.ofReal (Real.exp n) * (4:ℝ≥0∞)^n := by
      gcongr
      exact lintegral_quarterGaussian_le
    _ ≤ ENNReal.ofReal ((12:ℝ)^n) := by
      have he : Real.exp (n:ℝ) ≤ (3:ℝ)^n := by
        rw [← mul_one (n:ℝ), Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le n
      calc
        _ ≤ ENNReal.ofReal ((3:ℝ)^n) * (4:ℝ≥0∞)^n := mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl
        _ = _ := by rw [ENNReal.ofReal_pow (by norm_num), ← mul_pow]; norm_num

lemma cube_scaled_ball_volume (n : ℕ) (z : Space n) {r : ℝ} (hr : 0 < r) :
    volume (Metric.closedBall z (Real.sqrt n*r)) ≤ ENNReal.ofReal ((12:ℝ)^n*r^n) := by
  rw [Measure.addHaar_closedBall_center]
  have he : (WithLp.toLp 2 : (Fin n → ℝ) → Space n) ⁻¹' Metric.closedBall 0 (Real.sqrt n*r) =
      coordinateBall n (r*Real.sqrt n) := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right, coordinateBall, coordinateNorm, mul_comm]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage (show NullMeasurableSet (Metric.closedBall (0:Space n) (Real.sqrt n*r)) volume from Metric.isClosed_closedBall.measurableSet.nullMeasurableSet), he,
    volume_coordinateBall_smul n r (Real.sqrt n) hr]
  calc
    _ ≤ ENNReal.ofReal (r^n) * ENNReal.ofReal ((12:ℝ)^n) :=
      mul_le_mul' le_rfl (coordinate_ball_root_volume n)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

lemma cubeBall_volume (d : ℕ) (z : Space (d/2)) {r : ℝ} (hr : 0 < r) :
    CubeLaw d (CubeBall d z r) ≤ ENNReal.ofReal ((12:ℝ)^(d/2)*r^(d/2)) := by
  rw [CubeLaw, comap_subtype_coe_apply (cubeSet_measurable _)]
  apply (measure_mono (show Subtype.val '' CubeBall d z r ⊆ Metric.closedBall z (Real.sqrt (d/2:ℕ)*r) from ?_)).trans
    (cube_scaled_ball_volume (d/2) z hr)
  rintro _ ⟨u,hu,rfl⟩
  exact hu

lemma cube_cap_local {d : ℕ} (hd : 2 ≤ d) (y : Space d) {ε : ℝ} (hε : 0 < ε) :
    CubeLocal (fun u => capWeight y ε (CubeEmbedding d u))
      ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ)) := by
  intro z r hr
  let A : Set (Cube d) := CubeEmbedding d ⁻¹' Metric.closedBall y ε
  have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet.preimage (cubeEmbedding_measurable d)
  have hint : (∫⁻ u in CubeBall d z r, capWeight y ε (CubeEmbedding d u) ∂CubeLaw d) =
      CubeLaw d (A ∩ CubeBall d z r) := by
    change (∫⁻ u in CubeBall d z r, A.indicator (fun _ => (1:ℝ≥0∞)) u ∂CubeLaw d) = _
    rw [lintegral_indicator_const hA, one_mul, Measure.restrict_apply hA]
  rw [hint]
  have hεball : A ⊆ CubeBall d (Real.sqrt (d/2:ℕ) • cubeProject d y) ε := by
    intro u hu
    exact (cubeProject_parameter_dist hd u y).trans
      (mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _))
  have hs : (0:ℝ) ≤ (d/2:ℕ)/4 := by positivity
  have ht : (0:ℝ) ≤ 3*(d/2:ℕ)/4 := by positivity
  have he (t : ℝ) (ht : 0 < t) : t^(d/2) = t^((d/2:ℕ)/4:ℝ)*t^(3*(d/2:ℕ)/4:ℝ) := by
    rw [← Real.rpow_add ht, show ((d/2:ℕ)/4:ℝ)+(3*(d/2:ℕ)/4:ℝ) = (d/2:ℕ) by ring, Real.rpow_natCast]
  by_cases hh : r ≤ ε
  · apply ((measure_mono Set.inter_subset_right).trans (cubeBall_volume d z hr)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [he r hr, ← mul_assoc]
    gcongr
  · apply ((measure_mono (Set.inter_subset_left.trans hεball)).trans
      (cubeBall_volume d (Real.sqrt (d/2:ℕ) • cubeProject d y) hε)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [he ε hε, ← mul_assoc]
    gcongr
    exact le_of_not_ge hh

lemma cubeBall_univ (d : ℕ) : CubeBall d 0 1 = Set.univ := by
  ext u
  simp only [Set.mem_univ, iff_true]
  change dist u.val 0 ≤ Real.sqrt (d/2:ℕ)*1
  rw [dist_zero_right, mul_one]
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [← pow_two]
  rw [Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin (d/2), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := u.property i
      have hab := abs_le.mp h
      simp only [Real.norm_eq_abs, sq_abs]
      nlinarith
    _ = _ := by simp

lemma cube_mass_bound {d : ℕ} {f : Cube d → ℝ≥0∞} {L : ℝ} (h : CubeLocal f L) :
    (∫⁻ u, f u ∂CubeLaw d) ≤ ENNReal.ofReal L := by
  simpa [cubeBall_univ] using h 0 1 zero_lt_one

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
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeContinuation
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
lemma cubeStepConstant_one : 1 ≤ CubeStepConstant := (Classical.choose_spec cube_block).1
lemma cubeStepConstant_pos : 0 < CubeStepConstant := lt_of_lt_of_le zero_lt_one cubeStepConstant_one

lemma cubeStep_one (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ CubeStep d N := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ cubeStepConstant_one
  · exact Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
lemma cubeStep_pos (d : ℕ) {N : ℕ} (hN : 1 ≤ N) : 0 < CubeStep d N :=
  lt_of_lt_of_le zero_lt_one (cubeStep_one d hN)

lemma CubeLocal.mono {d : ℕ} {h : Cube d → ℝ≥0∞} {H K : ℝ}
    (hh : CubeLocal h H) (hHK : H ≤ K) : CubeLocal h K := by
  intro z r hr
  exact (hh z r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hHK (by positivity)))

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeArithmetic
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

lemma cube_memory_ratio {d M : ℕ} (hd : 16 ≤ d) (hM : M ≤ d^2) :
    (M:ℝ) / (((d/2)/4:ℕ):ℝ) ≤ 72 * (d/2:ℕ) := by
  have hd3 : d ≤ 3*(d/2) := by omega
  have hn8 : d/2 ≤ 8*((d/2)/4) := by omega
  have hm : M ≤ (72*(d/2))*((d/2)/4) := by
    calc
      M ≤ d^2 := hM
      _ ≤ (3*(d/2))^2 := Nat.pow_le_pow_left hd3 2
      _ = 9*(d/2)*(d/2) := by ring
      _ ≤ 9*(d/2)*(8*((d/2)/4)) := Nat.mul_le_mul_left _ hn8
      _ = _ := by ring
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < (d/2)/4 by omega))).2
  exact_mod_cast hm

lemma cube_memory_factor {d M : ℕ} (hd : 16 ≤ d) (hM : M ≤ d^2) :
    ((2^M:ℕ):ℝ)^(1/(((d/2)/4:ℕ):ℝ)) ≤ ((2:ℝ)^72)^(d/2) := by
  have he : ((2^M:ℕ):ℝ)^(1/(((d/2)/4:ℕ):ℝ)) =
      (2:ℝ)^((M:ℝ)/(((d/2)/4:ℕ):ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [he, ← pow_mul, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  simpa using cube_memory_ratio hd hM

lemma cube_stopping_factor {d : ℕ} (hd : 16 ≤ d) (T : ℕ) :
    (T+1:ℝ) ≤ ((2:ℝ)^(d/2))^BlockCount T ((d/2)/4) := by
  have hT := blockCount_mul_ge T (by omega : 0 < (d/2)/4)
  have hp : (d/2)/4 ≤ d/2 := Nat.div_le_self _ _
  have hTn : T ≤ (d/2) * BlockCount T ((d/2)/4) := by nlinarith
  have htwo : (T+1:ℕ) ≤ 2^T := Nat.lt_two_pow_self
  have hpow : (2:ℝ)^T ≤ 2^((d/2) * BlockCount T ((d/2)/4)) :=
    pow_le_pow_right₀ (by norm_num) hTn
  rw [pow_mul] at hpow
  exact (by exact_mod_cast htwo : (T+1:ℝ) ≤ (2:ℝ)^T).trans hpow

lemma cubeSuccessConstant_twelve : 12 ≤ CubeSuccessConstant := le_max_left _ _
lemma cubeSuccessConstant_one : 1 ≤ CubeSuccessConstant :=
  (by norm_num : (1:ℝ) ≤ 12).trans cubeSuccessConstant_twelve
lemma cubeSuccessConstant_exp : Real.exp 1 ≤ CubeSuccessConstant :=
  Real.exp_one_lt_three.le.trans ((by norm_num : (3:ℝ) ≤ 12).trans cubeSuccessConstant_twelve)
lemma cubeSuccessConstant_pos : 0 < CubeSuccessConstant :=
  lt_of_lt_of_le zero_lt_one cubeSuccessConstant_one

lemma cube_whole_factor {d M : ℕ} (hd : 16 ≤ d) (hM : M ≤ d^2) (T : ℕ) :
    (T+1:ℝ) * ((12:ℝ)^(d/2) * CubeStep d (2^M) ^ BlockCount T ((d/2)/4)) ≤
      CubeSuccessConstant^((d/2)*(BlockCount T ((d/2)/4)+1)) := by
  have hC := cubeStepConstant_pos
  have hD := cubeSuccessConstant_pos
  have hS := cubeStep_pos d (show 1 ≤ 2^M by exact one_le_pow₀ (by norm_num))
  have hmem := cube_memory_factor hd hM
  have hstep : (2:ℝ)^(d/2) * CubeStep d (2^M) ≤ CubeSuccessConstant^(d/2) := by
    calc
      _ ≤ 2^(d/2) * (CubeStepConstant^(d/2) * ((2:ℝ)^72)^(d/2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmem (by positivity)) (by positivity)
      _ = (2*CubeStepConstant*2^72)^(d/2) := by simp only [mul_pow]; ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  calc
    _ = 12^(d/2) * ((T+1:ℝ) * CubeStep d (2^M) ^ BlockCount T ((d/2)/4)) := by ring
    _ ≤ 12^(d/2) * (((2:ℝ)^(d/2))^BlockCount T ((d/2)/4) *
        CubeStep d (2^M) ^ BlockCount T ((d/2)/4)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (cube_stopping_factor hd T) (by positivity))
        (by positivity)
    _ = 12^(d/2) * ((2:ℝ)^(d/2) * CubeStep d (2^M))^BlockCount T ((d/2)/4) := by rw [mul_pow]
    _ ≤ CubeSuccessConstant^(d/2) * (CubeSuccessConstant^(d/2))^BlockCount T ((d/2)/4) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) cubeSuccessConstant_twelve _)
        (pow_le_pow_left₀ (by positivity) hstep _) (by positivity) (by positivity)
    _ = _ := by rw [pow_mul, pow_succ]; ring
end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeExperiment
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

lemma cubeSphere_measurable {d : ℕ} (hd : 2 ≤ d) : Measurable (CubeSphere hd) :=
  (cubeEmbedding_measurable d).subtype_mk

lemma cubeAmbient_support {d : ℕ} (hd : 2 ≤ d) : (CubeAmbient d).support ⊆ Metric.closedBall 0 1 := by
  apply Measure.support_subset_of_isClosed Metric.isClosed_closedBall
  rw [mem_ae_iff, CubeAmbient, Measure.map_apply (cubeEmbedding_measurable d)
    Metric.isClosed_closedBall.measurableSet.compl]
  have he : CubeEmbedding d ⁻¹' (Metric.closedBall (0:Space d) 1)ᶜ = ∅ := by
    ext u
    simp [cubeEmbedding_norm hd, Metric.mem_closedBall, dist_zero_right]
  rw [he, measure_empty]

lemma cubeAmbient_polynomial {d : ℕ} (hd : 2 ≤ d) :
    PolynomialMass (CubeAmbient d) (d/2) (ENNReal.ofReal ((12:ℝ)^(d/2))) := by
  intro x r hr
  rw [CubeAmbient, Measure.map_apply (cubeEmbedding_measurable d) Metric.isClosed_closedBall.measurableSet]
  have hsub : CubeEmbedding d ⁻¹' Metric.closedBall x r ⊆
      CubeBall d (Real.sqrt (d/2:ℕ) • cubeProject d x) r := by
    intro u hu
    exact (cubeProject_parameter_dist hd u x).trans
      (mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _))
  exact ((measure_mono hsub).trans (cubeBall_volume d _ hr)).trans_eq (ENNReal.ofReal_mul (by positivity))

lemma cube_observation_quasi {d : ℕ} (hd : 16 ≤ d) :
    Measure.QuasiMeasurePreserving
      (fun z : Cube d × Space d => (z.2,⟪CubeEmbedding d z.1,z.2⟫))
      ((CubeLaw d).prod (stdGaussian (Space d))) (observationReference d) := by
  have hac : projectionLaw (CubeAmbient d) 1 ≪ matrixLabelReference (E := Space d) 1 := by
    apply projectionLaw_absolutelyContinuous (cubeAmbient_polynomial (by omega : 2 ≤ d))
      (C := ENNReal.ofReal ((12:ℝ)^(d/2))) (n := 1)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact cubeAmbient_support (by omega)
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → Space d) × Space d => (z.1,fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian (Space d))).prod (CubeAmbient d))
      (matrixLabelReference (E := Space d) 1) := ⟨by fun_prop,hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian (Space d)) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) (Space d))).prod
    ((cubeEmbedding_measurable d).measurePreserving (CubeLaw d))
  have h2 := (measurePreserving_funUnique (stdGaussian (Space d)) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  · ext z <;> simp [MeasurableEquiv.funUnique]
  · rfl

lemma cube_sample_observation_quasi {d T : ℕ} (hd : 16 ≤ d) (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : Cube d × Samples d T => (z.2 i,⟪CubeEmbedding d z.1,z.2 i⟫))
      ((CubeLaw d).prod (sampleLaw d T)) (observationReference d) := by
  exact (cube_observation_quasi hd).comp
    ((MeasurePreserving.id (CubeLaw d)).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian (Space d)) i)).quasiMeasurePreserving

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

lemma measurable_angleTest (ε : ℝ) : Measurable (angleTest (d := d) ε) := by
  unfold angleTest
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    measurable_const measurable_const
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

lemma output_chord_cube_local (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (j : MemoryPrecision.Kernel.State M) :
    CubeLocal (fun u => K.outputTest (chordTest ε) t j (CubeSphere hd u))
      ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ)) := by
  intro z r hr
  change (∫⁻ u in CubeBall d z r, ∫⁻ v, chordTest ε (CubeSphere hd u,v)
    ∂K.output t j ∂CubeLaw d) ≤ _
  have hf : Measurable (Function.uncurry (fun (u : Cube d) (v : MemoryPrecision.Kernel.Sphere d) =>
      chordTest ε (CubeSphere hd u,v))) :=
    (measurable_chordTest ε).comp ((cubeSphere_measurable hd).comp measurable_fst |>.prodMk measurable_snd)
  rw [lintegral_lintegral_swap hf.aemeasurable]
  simp_rw [chordTest_eq_cap]
  change (∫⁻ v : MemoryPrecision.Kernel.Sphere d, ∫⁻ u in CubeBall d z r,
      capWeight v.val ε (CubeEmbedding d u) ∂CubeLaw d ∂K.output t j) ≤ _
  have hb (v : MemoryPrecision.Kernel.Sphere d) := cube_cap_local hd v.val hε z r hr
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

lemma stoch_cube_mass {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N → ℝ≥0∞}
    {w : ℕ → Fin N → Cube d → ℝ≥0∞}
    (hδ : ∀ n j a, Measurable (fun obs => δ n j obs a))
    (hδ1 : ∀ n j obs, ∑ a, δ n j obs a ≤ 1) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1) {H : ℝ} (hH : 0 < H)
    (hlocal : ∀ n j, CubeLocal (w n j) H)
    (b k : ℕ) (hk : k ≤ b*((d/2)/4)) (n : ℕ) (j : Fin N) :
    CubeLocal (stochCont δ w (CubeEmbedding d) n k j)
      (H * CubeStep d N ^ b) := by
  have hp : 0 < (d/2)/4 := by omega
  have hK := cubeStep_one d hN
  have hK0 := cubeStep_pos d hN
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
    · let m := min k ((d/2)/4)
      have hm : 1 ≤ m := by dsimp [m]; omega
      have hmp : m ≤ (d/2)/4 := min_le_right _ _
      have hmk : m ≤ k := min_le_left _ _
      have hk' : k-m ≤ b*((d/2)/4) := by
        dsimp [m]
        rw [Nat.succ_mul] at hk
        omega
      have hb := (Classical.choose_spec cube_block).2 d m N hd hm hmp hN
        (H * CubeStep d N ^ b) (mul_pos hH (pow_pos hK0 b)).le
        (fun a => stochCont δ w (CubeEmbedding d) (n+m) (k-m) a)
        (fun a => measurable_stochCont hδ hw (cubeEmbedding_measurable d) _ _ a)
        (fun a s => stochCont_le_one (CubeEmbedding d) hδ1 hw1 _ _ a s)
        (fun a => ih (k-m) hk' (n+m) a)
        (fun a x => stochRoute δ n m j x a)
        (fun a => measurable_stochRoute hδ n m j a)
        (fun x => stochRoute_sum_le_one hδ1 n m j x)
      have he : stochCont δ w (CubeEmbedding d) n k j =
          WeightedBlock (CubeEmbedding d)
            (fun a => stochCont δ w (CubeEmbedding d) (n+m) (k-m) a)
            (fun a x => stochRoute δ n m j x a) := by
        funext s
        simpa [Nat.add_sub_of_le hmk, WeightedBlock] using
          stochCont_unroll (CubeEmbedding d) hδ n m (k-m) j s
      rw [he]
      convert hb using 1
      change H * CubeStep d N ^ (b+1) = CubeStep d N * (H * CubeStep d N ^ b)
      rw [pow_succ]; ring

end MemoryPrecision


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelCube
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

instance instIsProbabilityMeasureElemVectorSphereCubePrior {d : ℕ} (hd : 2 ≤ d) : IsProbabilityMeasure (CubePrior hd) := by
  unfold CubePrior
  exact Measure.isProbabilityMeasure_map (cubeSphere_measurable hd).aemeasurable

lemma cubeSphere_preserving {d : ℕ} (hd : 2 ≤ d) :
    MeasurePreserving (CubeSphere hd) (CubeLaw d) (CubePrior hd) :=
  ⟨cubeSphere_measurable hd, rfl⟩

namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma eval_comp {X Y : Type*} (w : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞) (ι : Y → X)
    (n k : ℕ) (j : MemoryPrecision.Kernel.State M) (s : Y) (obs : Observations d k) :
    K.eval w n k j (ι s) obs = K.eval (fun n j s => w n j (ι s)) n k j s obs := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    simp only [eval]
    apply Finset.sum_congr rfl
    intro a _
    rw [ih]
lemma pathValue_comp {X Y : Type*} (w : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞) (ι : Y → X)
    (s : Y) (obs : Observations d T) :
    K.pathValue w (ι s) obs = K.pathValue (fun n j s => w n j (ι s)) s obs := by
  simp only [pathValue, K.eval_comp w ι]

lemma borel_cube_bound (hK : K.Borel) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : Cube d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) (CubeSphere (d := d) (by omega) z.1)
        (records (CubeSphere (d := d) (by omega) z.1) z.2)
      ∂(CubeLaw d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) *
        CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) := by
  have hm₁ : Measurable (fun z : Cube d × Rows d T =>
      (CubeSphere (d := d) (by omega) z.1,z.2)) :=
    ((cubeSphere_measurable (d := d) (by omega)).comp measurable_fst).prodMk measurable_snd
  have hm₀ := K.experiment_fixed_measurable (f := chordTest (d := d) ε) hK (measurable_chordTest ε)
  have hm := hm₀.comp hm₁
  have hprod := lintegral_prod (μ := CubeLaw d) (ν := RowLaw d T) _ hm.aemeasurable
  simp only [Function.comp_apply] at hprod
  rw [hprod]
  simp_rw [K.pathValue_comp _ (CubeSphere (d := d) (by omega))]
  apply K.integral_pathValue_bound (fun n j u => K.outputTest (chordTest ε) n j (CubeSphere (d := d) (by omega) u))
    (CubeEmbedding d) hK
    (fun n j => (K.outputTest_measurable (measurable_chordTest ε) n j).comp (cubeSphere_measurable (d := d) (by omega)))
    (cubeEmbedding_measurable d) (CubeLaw d)
  intro r hr j
  apply cube_mass_bound
  exact stoch_cube_mass hd (show 1 ≤ 2^M from one_le_pow₀ (by norm_num))
    (K.marginal_measurable hK) (fun n j obs => (K.marginal_sum n j obs).le)
    (fun n j => (K.outputTest_measurable (measurable_chordTest ε) n j).comp (cubeSphere_measurable (d := d) (by omega)))
    (fun n j u => K.outputTest_le_one (chordTest_le_one ε) n j (CubeSphere (d := d) (by omega) u))
    (by positivity) (K.output_chord_cube_local (by omega) hε)
    (MemoryPrecision.BlockCount T ((d/2)/4)) r
    (hr.trans (blockCount_mul_ge T (by omega))) 0 j

lemma completed_cube_bound (hK : K.Completed) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ z : Cube d × Rows d T,
      K.pathValue (K.outputTest (chordTest ε)) (CubeSphere (d := d) (by omega) z.1)
        (records (CubeSphere (d := d) (by omega) z.1) z.2)
      ∂(CubeLaw d).prod (RowLaw d T)) ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) *
        CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) := by
  have he := K.version_pathValue_ae ((CubeLaw d).prod (RowLaw d T)) hK
    (fun z : Cube d × Rows d T => CubeSphere (d := d) (by omega) z.1)
    (fun z : Cube d × Rows d T => records (CubeSphere (d := d) (by omega) z.1) z.2)
    (fun i => show Measure.QuasiMeasurePreserving _ _ _ from cube_sample_observation_quasi hd i)
    (chordTest ε)
  rw [← lintegral_congr_ae he]
  exact (K.version hK).borel_cube_bound (K.version_borel hK) hd hε

lemma source_cube_chord_bound {Ω : Type u} [MeasurableSpace Ω] (L : Ω → Policy d M T)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (hd : 16 ≤ d)
    (hL : Admissible L ρ (CubePrior (by omega))) {ε : ℝ} (hε : 0 < ε) :
    ChordSuccess L ρ (CubePrior (by omega)) ε ≤
      (T+1:ℝ≥0∞)*ENNReal.ofReal ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) *
        CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) := by
  have hp := (cubeSphere_preserving (by omega : 2 ≤ d)).prod
    (MeasurePreserving.id (ρ.prod (RowLaw d T)))
  have hf := hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε)
  have he : (∫⁻ z : Cube d × (Ω × Rows d T),
      experiment L (chordTest ε) (CubeSphere (d := d) (by omega) z.1,z.2)
      ∂(CubeLaw d).prod (ρ.prod (RowLaw d T))) = ChordSuccess L ρ (CubePrior (by omega)) ε := by
    calc
      _ = ∫⁻ z, experiment L (chordTest ε) z ∂((CubeLaw d).prod (ρ.prod (RowLaw d T))).map
          (Prod.map (CubeSphere (d := d) (by omega)) id) :=
        (lintegral_map' (by simpa only [hp.map_eq] using hf) hp.measurable.aemeasurable).symm
      _ = _ := by rw [hp.map_eq]; rfl
  rw [← he]
  apply seed_average_bound (CubeLaw d) (RowLaw d T) ρ
    (hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving)
  filter_upwards [hL.completed] with ω hω
  exact (L ω).completed_cube_bound hω hd hε
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
-- module Solutions.OAIQ1_Mem.MemoryPrecision_KernelSphere
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereCubePrior
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
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_Reflection
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereCubePrior
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
open NoiselessRegression
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma eval_pair_le_one {X : Type*} (w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞)
    (s t : X) (hpair : ∀ n j, w n j s + v n j t ≤ 1)
    (n k : ℕ) (j : MemoryPrecision.Kernel.State M) (obs : Observations d k) :
    K.eval w n k j s obs + K.eval v n k j t obs ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hpair n j
  | succ k ih =>
    simp only [eval, ← Finset.sum_add_distrib, ← mul_add]
    calc
      _ ≤ ∑ a : Action M, K.transition (n+1) j (obs 0) a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul' le_rfl
        split_ifs
        · exact hpair _ _
        · exact ih _ _ _
      _ = 1 := by simpa only [mul_one] using K.transition_sum (n+1) j (obs 0)

lemma pathValue_pair_le_one {X : Type*} (w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞)
    (s t : X) (hpair : ∀ n j, w n j s + v n j t ≤ 1) (obs : Observations d T) :
    K.pathValue w s obs + K.pathValue v t obs ≤ 1 := by
  simp only [pathValue, ← Finset.sum_add_distrib, ← mul_add]
  calc
    _ ≤ ∑ a : Action M, K.initial a * 1 := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul' le_rfl
      split_ifs
      · exact hpair _ _
      · exact K.eval_pair_le_one w v s t hpair _ _ _ _
    _ = 1 := by simpa only [mul_one] using K.initial_sum

lemma chord_pair_le_one {ε : ℝ} (hε : ε ≤ 1/10)
    (s t v : MemoryPrecision.Kernel.Sphere d) (hst : 1/5 < dist s.val t.val) :
    chordTest ε (s,v) + chordTest ε (t,v) ≤ 1 := by
  classical
  have hn : ¬(dist v.val s.val ≤ ε ∧ dist v.val t.val ≤ ε) := by
    rintro ⟨hs,ht⟩
    have htri := dist_triangle s.val v.val t.val
    rw [dist_comm s.val v.val] at htri
    linarith
  simp only [chordTest, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

lemma output_chord_pair_le_one {ε : ℝ} (hε : ε ≤ 1/10)
    (s t : MemoryPrecision.Kernel.Sphere d) (hst : 1/5 < dist s.val t.val)
    (n : ℕ) (j : MemoryPrecision.Kernel.State M) :
    K.outputTest (chordTest ε) n j s + K.outputTest (chordTest ε) n j t ≤ 1 := by
  have hm : Measurable (fun v : MemoryPrecision.Kernel.Sphere d => chordTest ε (s,v)) :=
    (measurable_chordTest ε).comp (measurable_const.prodMk measurable_id)
  simp only [outputTest]
  rw [← lintegral_add_left hm]
  exact (lintegral_mono (fun v => chord_pair_le_one hε s t v hst)).trans_eq (by simp)

lemma path_reflection_pair {ε : ℝ} (hε : ε ≤ 1/10)
    (A : Rows d T) (s : MemoryPrecision.Kernel.Sphere d)
    (U : Submodule ℝ (MemoryPrecision.Kernel.Vector d)) (hA : ∀ i, A i ∈ U)
    (hst : 1/5 < dist s.val (U.reflection s.val)) :
    K.pathValue (K.outputTest (chordTest ε)) s (records s A) +
      K.pathValue (K.outputTest (chordTest ε)) (sphereIsometry U.reflection s)
        (records (sphereIsometry U.reflection s) A) ≤ 1 := by
  have he : records (sphereIsometry U.reflection s) A = records s A := by
    funext i
    change (A i, ⟪U.reflection s.val, A i⟫) = (A i, ⟪s.val, A i⟫)
    apply Prod.ext
    · rfl
    · have h := U.reflection.inner_map_map s.val (A i)
      rw [(Submodule.reflection_eq_self_iff (A i)).2 (hA i)] at h
      exact h
  rw [he]
  have hpair : ∀ n j, K.outputTest (chordTest ε) n j s +
      K.outputTest (chordTest ε) n j (sphereIsometry U.reflection s) ≤ 1 :=
    fun n j => K.output_chord_pair_le_one hε s (sphereIsometry U.reflection s) hst n j
  exact K.pathValue_pair_le_one (K.outputTest (chordTest ε))
    (K.outputTest (chordTest ε)) s (sphereIsometry U.reflection s) hpair (records s A)
end Policy

lemma sphere_reflection_function_bound {d : ℕ} [NeZero d]
    (U : Submodule ℝ (MemoryPrecision.Kernel.Vector d)) (hU : 4*Module.finrank ℝ U ≤ d)
    {f : MemoryPrecision.Kernel.Sphere d → ℝ≥0∞} (hf : AEMeasurable f (UniformSphere d))
    (hf1 : ∀ s, f s ≤ 1)
    (hpair : ∀ s, 1/5 < dist s.val (U.reflection s.val) →
      f s + f (sphereIsometry U.reflection s) ≤ 1) :
    (∫⁻ s, f s ∂UniformSphere d) ≤ ENNReal.ofReal (21/32:ℝ) := by
  let R := sphereIsometry U.reflection
  let B : Set (MemoryPrecision.Kernel.Sphere d) := {s | (4/5:ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2}
  have hB : MeasurableSet B := by dsimp [B]; exact measurableSet_le measurable_const (by fun_prop)
  have hp : MeasurePreserving R (UniformSphere d) (UniformSphere d) := sphereIsometry_preserving U.reflection
  have he : (∫⁻ s, f (R s) ∂UniformSphere d) = ∫⁻ s, f s ∂UniformSphere d := by
    calc
      _ = ∫⁻ s, f s ∂(UniformSphere d).map R :=
        (lintegral_map' (by simpa only [hp.map_eq] using hf) hp.measurable.aemeasurable).symm
      _ = _ := by rw [hp.map_eq]
  have hb : UniformSphere d B ≤ ENNReal.ofReal (5/16:ℝ) :=
    sphere_projection_large U (by simpa using hU)
  have hsum : ∀ s, f s + f (R s) ≤ 1 + B.indicator (fun _ => 1) s := by
    intro s
    classical
    by_cases hs : s ∈ B
    · simpa [hs] using add_le_add (hf1 s) (hf1 (R s))
    · have hst : 1/5 < dist s.val (U.reflection s.val) := by
        by_contra hn
        have hd : dist s.val (U.reflection s.val) ≤ 1/5 := le_of_not_gt hn
        rw [reflection_dist] at hd
        have hn := U.norm_sq_eq_add_norm_sq_starProjection s.val
        rw [mem_sphere_zero_iff_norm.mp s.property] at hn
        have he : ‖U.starProjection s.val‖ = ‖U.orthogonalProjectionOnto s.val‖ := rfl
        rw [he] at hn
        apply hs
        change (4/5:ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2
        nlinarith [norm_nonneg (Uᗮ.starProjection s.val)]
      simpa [hs] using hpair s hst
  have hi : (∫⁻ s, f s ∂UniformSphere d) + (∫⁻ s, f s ∂UniformSphere d) ≤
      1 + ENNReal.ofReal (5/16:ℝ) := by
    calc
      _ = (∫⁻ s, f s ∂UniformSphere d) + (∫⁻ s, f (R s) ∂UniformSphere d) := by rw [he]
      _ = ∫⁻ s, f s + f (R s) ∂UniformSphere d := (lintegral_add_left' hf _).symm
      _ ≤ ∫⁻ s, 1 + B.indicator (fun _ => (1:ℝ≥0∞)) s ∂UniformSphere d := lintegral_mono hsum
      _ = 1 + UniformSphere d B := by rw [lintegral_add_left measurable_const]; simp [lintegral_indicator_const hB]
      _ ≤ _ := add_le_add le_rfl hb
  calc
    _ = ENNReal.ofReal (1/2:ℝ) * ((∫⁻ s, f s ∂UniformSphere d) +
      (∫⁻ s, f s ∂UniformSphere d)) := by
      rw [← two_mul, ← mul_assoc]
      have hc : ENNReal.ofReal (1/2:ℝ) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
        norm_num
      rw [hc, one_mul]
    _ ≤ ENNReal.ofReal (1/2:ℝ) * (1 + ENNReal.ofReal (5/16:ℝ)) := mul_le_mul' le_rfl hi
    _ = ENNReal.ofReal (21/32:ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1)
        (by norm_num : (0:ℝ) ≤ 5/16),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
      norm_num

namespace Policy
lemma source_linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10)
    (hL : Admissible L ρ (UniformSphere d)) :
    Success L ρ (UniformSphere d) ε ≤ ENNReal.ofReal (21/32:ℝ) := by
  let : NeZero d := ⟨hd.ne'⟩
  apply (success_le_chord L ρ (UniformSphere d) ε).trans
  have hm := hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε)
  unfold ChordSuccess
  rw [lintegral_prod_symm _ hm]
  apply le_trans (b := ∫⁻ _z : Ω × Rows d T, ENNReal.ofReal (21/32:ℝ)
    ∂ρ.prod (RowLaw d T)) ?_ (by simp)
  apply lintegral_mono_ae
  filter_upwards [ae_fiber_aemeasurable hm] with z hz
  let U : Submodule ℝ (MemoryPrecision.Kernel.Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  apply sphere_reflection_function_bound U ((Nat.mul_le_mul_left 4 hdim).trans hT) hz
  · intro s
    exact (L z.1).pathValue_le_one _ ((L z.1).outputTest_le_one (chordTest_le_one ε)) _ _
  · intro s hs
    exact (L z.1).path_reflection_pair hε z.2 s U
      (fun i => Submodule.subset_span (Set.mem_range_self i)) hs
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_Precision
attribute [-instance] _root_.OAI.MemoryPrecision.Kernel.instIsProbabilityMeasureElemVectorSphereCubePrior
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

lemma precision_from_exact_bound {d M T : ℕ} {ε C A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hC : 0 < C) (hA : 0 < A)
    (hM : (M:ℝ) ≤ A*(d:ℝ)^2) (hε : 0 < ε)
    (hb : (2/3:ℝ) ≤
      (2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)) :
    (1/(8+20*C*(1+A)))*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdp : (d:ℝ) ≤ 4*T := by exact_mod_cast hT
  let q := (d-1)/8
  let b := BlockCount T q
  let a := ((d:ℝ)-1)/2
  let X := C*(1+(M:ℝ)/(d:ℝ)^2)*(b:ℝ)
  have hq : 0 < q := by dsimp [q]; omega
  have hdq : (d:ℝ) ≤ 16*(q:ℝ) := by
    exact_mod_cast (show d ≤ 16*q by dsimp [q]; omega)
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hbd : (b:ℝ)*(d:ℝ) ≤ 20*T := by
    have hceil : (b:ℝ) ≤ (T:ℝ)/q+1 :=
      (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ (T:ℝ)/q)).le
    calc
      _ ≤ ((T:ℝ)/q+1)*d := mul_le_mul_of_nonneg_right hceil hd0.le
      _ = ((T:ℝ)/q)*d+d := by ring
      _ ≤ ((T:ℝ)/q)*(16*q)+d := by gcongr
      _ = 16*T+d := by field_simp
      _ ≤ _ := by linarith
  have ha : 1 ≤ a := by
    dsimp [a]
    have : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ha0 : 0 < a := by linarith
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2/3) hb
  change Real.log (2/3:ℝ) ≤ Real.log ((2*ε*Real.exp X)^a) at hlog
  rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_mul (by norm_num) hε.ne'] at hlog
  have hl2 : Real.log 2 ≤ (1:ℝ) := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2) using 1
    norm_num
  have hl23 : -(1:ℝ) ≤ Real.log (2/3:ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2/3)
    norm_num at h
    linarith
  have hle : Real.log (1/ε) ≤ 2+X := by
    have hmul := mul_le_mul_of_nonneg_left hl2 ha0.le
    have he : Real.log (1/ε) = -Real.log ε := by simp
    rw [he]
    nlinarith
  have hmem : (M:ℝ)/(d:ℝ)^2 ≤ A := (div_le_iff₀ (sq_pos_of_pos hd0)).2 hM
  have hX : X*(d:ℝ) ≤ 20*C*(1+A)*T := by
    calc
      _ = C*(1+(M:ℝ)/(d:ℝ)^2)*((b:ℝ)*d) := by dsimp [X]; ring
      _ ≤ C*(1+A)*((b:ℝ)*d) := by gcongr
      _ ≤ C*(1+A)*(20*T) := mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = _ := by ring
  have hfinal : (d:ℝ)*Real.log (1/ε) ≤ (8+20*C*(1+A))*T := by
    have hh := mul_le_mul_of_nonneg_left hle hd0.le
    nlinarith
  have hp : 0 < 8+20*C*(1+A) := by positivity
  calc
    _ = ((d:ℝ)*Real.log (1/ε))/(8+20*C*(1+A)) := by ring
    _ ≤ _ := (div_le_iff₀ hp).2 (by nlinarith)

namespace Policy
lemma source_uniform_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hL : Admissible L ρ (UniformSphere d)) (ε : ℝ)
    (hs : ∀ s, (2/3:ℝ≥0∞) ≤ FixedSuccess L ρ ε s) :
    (2/3:ℝ≥0∞) ≤ Success L ρ (UniformSphere d) ε := by
  let : NeZero d := ⟨hd.ne'⟩
  have hm := hL.experiment (angleTest ε) (measurable_angleTest ε) (angleTest_le_one ε)
  unfold Success
  rw [lintegral_prod _ hm]
  calc
    _ = ∫⁻ _s : MemoryPrecision.Kernel.Sphere d, (2/3:ℝ≥0∞) ∂UniformSphere d := by simp
    _ ≤ _ := lintegral_mono hs

lemma source_precision {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 32 ≤ d) (hL : Admissible L ρ (UniformSphere d)) {ε A : ℝ}
    (hA : 0 < A) (hM : (M:ℝ) ≤ A*(d:ℝ)^2) (hε : 0 < ε) (hε1 : ε ≤ 1/10)
    (hs : (2/3:ℝ≥0∞) ≤ Success L ρ (UniformSphere d) ε) :
    (1/(8+20*StreamConstant*(1+A)))*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ) := by
  have hT : d ≤ 4*T := by
    by_contra hn
    have hb := hs.trans (source_linear_success_bound L ρ (by omega) (by omega) hε1 hL)
    have hb' : ENNReal.ofReal (2/3:ℝ) ≤ ENNReal.ofReal (21/32:ℝ) := by
      simpa [ENNReal.ofReal_div_of_pos] using hb
    have hh := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 21/32)).mp hb'
    norm_num at hh
  have hb := hs.trans (source_stream_explicit d M T hd ε hε hε1 Ω ρ inferInstance L hL)
  have hb' : (2/3:ℝ) ≤
      (2*ε*Real.exp (StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa [ENNReal.ofReal_div_of_pos] using hb.trans (min_le_right _ _)
  exact precision_from_exact_bound hd hT streamConstant_pos hA hM hε hb'
end Policy
end MemoryPrecision.Kernel


end

end OAI
end

section
-- module Solutions.OAIQ1_Mem.MemoryPrecision_CubeSuccess
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
open MemoryPrecision NoiselessRegression Policy

lemma source_cube_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 16 ≤ d) (hL : Admissible L ρ (CubePrior (by omega)))
    (hM : M ≤ d^2) {ε : ℝ} (hε : 0 < ε) :
    Success L ρ (CubePrior (by omega)) ε ≤ min 1 (ENNReal.ofReal
      (CubeSuccessConstant^((d/2)*(BlockCount T ((d/2)/4)+1)) * ε^((d/2:ℕ)/4:ℝ))) := by
  refine le_min (Policy.success_le_one L ρ (CubePrior (by omega)) ε) ?_
  have hb := (Policy.success_le_chord L ρ (CubePrior (by omega)) ε).trans
    (Policy.source_cube_chord_bound L ρ hd hL hε)
  have he : (T+1:ℝ≥0∞) * ENNReal.ofReal
      ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) * CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4)) =
      ENNReal.ofReal ((T+1:ℝ) *
        ((12:ℝ)^(d/2)*ε^((d/2:ℕ)/4:ℝ) * CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4))) := by
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ T+1)]
    congr 1
    simp [ENNReal.ofReal_add]
  rw [he] at hb
  apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ = ((T+1:ℝ) * ((12:ℝ)^(d/2) * CubeStep d (2^M)^MemoryPrecision.BlockCount T ((d/2)/4))) *
        ε^((d/2:ℕ)/4:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (cube_whole_factor hd hM T) (by positivity)

theorem source_cube_success_oai : SourceCubeStatement := by
  refine ⟨CubeSuccessConstant,cubeSuccessConstant_exp,32,by norm_num,
    1/(8+20*StreamConstant*(1+1)),by have := streamConstant_pos; positivity,?_⟩
  intro d M T hd hM ε hε hε1 Ω _ ρ hρ L hL
  have : IsProbabilityMeasure ρ := hρ
  let : NeZero d := ⟨by omega⟩
  refine ⟨source_cube_bound L ρ (by omega) (hL _ inferInstance) hM hε, ?_⟩
  intro hs
  apply Policy.source_precision L ρ hd (hL _ inferInstance) (by norm_num : (0:ℝ) < 1)
    (by exact_mod_cast (by simpa using hM : M ≤ 1*d^2)) hε hε1
  exact Policy.source_uniform_of_pointwise L ρ (by omega) (hL _ inferInstance) ε hs
end MemoryPrecision.Kernel


end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MemoryPrecision.Kernel.source_cube_success_oai.{u_1} := @OAI.MemoryPrecision.Kernel.source_cube_success_oai.{u_1}
