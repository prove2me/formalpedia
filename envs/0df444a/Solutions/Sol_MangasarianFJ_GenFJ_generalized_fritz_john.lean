-- Prove2me | solution 1 for MangasarianFJ.GenFJ.generalized_fritz_john
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T07:52:13.019496+00:00
-- url     : https://prove2.me/submissions/2c787cef-cd41-439f-ab0c-3e9548fa2e7b

-- SPDX-License-Identifier: Apache-2.0
import Mathlib
import Definitions.Def_MangasarianFJ_GenFJ_Setting


-- Complete module: FJProof/SharedBasics.lean

open scoped BigOperators

namespace MangasarianFJ.GenFJ.FJFresh

noncomputable def violation {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (x : E) : ℝ :=
  ∑ i, (max (g i x) 0) ^ 2 + ∑ j, (h j x) ^ 2

noncomputable def penalized {E : Type*} [NormedAddCommGroup E]
    (θ R : E → ℝ) (bar : E) (j : ℕ) (x : E) : ℝ :=
  θ x + ‖x - bar‖ ^ 2 + ((j : ℝ) + 1) * R x

theorem violation_nonneg {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (x : E) :
    0 ≤ violation g h x :=
  add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem violation_eq_zero_iff {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (x : E) :
    violation g h x = 0 ↔ (∀ i, g i x ≤ 0) ∧ ∀ j, h j x = 0 := by
  classical
  unfold violation
  rw [add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg (_ : ℝ)),
    Finset.mem_univ, true_implies, sq_eq_zero_iff, max_eq_right_iff]

theorem continuous_violation {E : Type*} [TopologicalSpace E] {m k : ℕ}
    {g : Fin m → E → ℝ} {h : Fin k → E → ℝ}
    (hg : ∀ i, Continuous (g i)) (hh : ∀ j, Continuous (h j)) :
    Continuous (violation g h) := by
  unfold violation
  fun_prop

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/PenaltyMinimizers.lean

noncomputable section
namespace MangasarianFJ.GenFJ.FJFresh
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

theorem exists_penalty_minimizers (θ R : E → ℝ) (bar : E)
    (hθ : Continuous θ) (hR : Continuous R) :
    ∃ x : ℕ → E, ∀ j, x j ∈ Metric.closedBall bar 1 ∧
      IsMinOn (penalized θ R bar j) (Metric.closedBall bar 1) (x j) := by
  have hex : ∀ j : ℕ, ∃ z ∈ Metric.closedBall bar 1,
      IsMinOn (penalized θ R bar j) (Metric.closedBall bar 1) z := by
    intro j
    apply (isCompact_closedBall bar 1).exists_isMinOn
      ⟨bar, Metric.mem_closedBall_self (by norm_num)⟩
    unfold penalized
    fun_prop
  choose x hx hm using hex
  exact ⟨x, fun j => ⟨hx j, hm j⟩⟩

omit [ProperSpace E] in
theorem penalty_minimizer_bound (θ R : E → ℝ) (bar z : E) (j : ℕ)
    (hRbar : R bar = 0)
    (hm : IsMinOn (penalized θ R bar j) (Metric.closedBall bar 1) z) :
    θ z + ‖z - bar‖ ^ 2 + ((j : ℝ) + 1) * R z ≤ θ bar := by
  have h := hm (Metric.mem_closedBall_self (show (0 : ℝ) ≤ 1 by norm_num))
  change penalized θ R bar j z ≤ penalized θ R bar j bar at h
  simpa only [penalized, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    hRbar, mul_zero, add_zero] using h

theorem penalty_violation_tendsto (θ R : E → ℝ) (bar : E)
    (hθ : Continuous θ) (hR0 : ∀ z, 0 ≤ R z) (hRbar : R bar = 0)
    (x : ℕ → E) (hx : ∀ j, x j ∈ Metric.closedBall bar 1)
    (hm : ∀ j, IsMinOn (penalized θ R bar j) (Metric.closedBall bar 1) (x j)) :
    Tendsto (fun j => R (x j)) atTop (𝓝 0) := by
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall bar 1).exists_isMinOn
    ⟨bar, Metric.mem_closedBall_self (by norm_num)⟩ hθ.continuousOn
  have hb : ∀ j, R (x j) ≤ (θ bar - θ z) / ((j : ℝ) + 1) := by
    intro j
    apply (le_div_iff₀ (show (0 : ℝ) < (j : ℝ) + 1 by positivity)).mpr
    have hp := penalty_minimizer_bound θ R bar (x j) j hRbar (hm j)
    have hl : θ z ≤ θ (x j) := hz (hx j)
    nlinarith [sq_nonneg ‖x j - bar‖]
  have ht : Tendsto (fun j : ℕ => (θ bar - θ z) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (θ bar - θ z)).comp
        (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun j => hR0 (x j)) hb ht

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/PenaltyExtraction.lean

noncomputable section
namespace MangasarianFJ.GenFJ.FJFresh
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

 theorem penalty_product_subsequence {C : Type*} [MetricSpace C]
    (θ R : E → ℝ) (bar : E) (hθ : Continuous θ) (hR : Continuous R)
    (hR0 : ∀ z, 0 ≤ R z) (hRbar : R bar = 0)
    (hopt : ∀ z, R z = 0 → θ bar ≤ θ z)
    (x : ℕ → E) (hx : ∀ j, x j ∈ Metric.closedBall bar 1)
    (hm : ∀ j, IsMinOn (penalized θ R bar j) (Metric.closedBall bar 1) (x j))
    (K : Set C) (hK : IsCompact K) (c : ℕ → C) (hc : ∀ j, c j ∈ K) :
    ∃ l ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 bar) ∧ Tendsto (c ∘ φ) atTop (𝓝 l) := by
  obtain ⟨p, hp, φ, hφ, ht⟩ := ((isCompact_closedBall bar 1).prod hK).tendsto_subseq
    (x := fun j => (x j, c j)) (fun j => ⟨hx j, hc j⟩)
  have hxt : Tendsto (x ∘ φ) atTop (𝓝 p.1) := continuous_fst.tendsto p |>.comp ht
  have hct : Tendsto (c ∘ φ) atTop (𝓝 p.2) := continuous_snd.tendsto p |>.comp ht
  have hr := (penalty_violation_tendsto θ R bar hθ hR0 hRbar x hx hm).comp
    hφ.tendsto_atTop
  have hrp : R p.1 = 0 := tendsto_nhds_unique ((hR.tendsto p.1).comp hxt) hr
  have hbound : ∀ j, θ (x j) + ‖x j - bar‖ ^ 2 ≤ θ bar := by
    intro j
    have hb := penalty_minimizer_bound θ R bar (x j) j hRbar (hm j)
    have hn : 0 ≤ ((j : ℝ) + 1) * R (x j) := mul_nonneg (by positivity) (hR0 _)
    linarith
  have hb : θ p.1 + ‖p.1 - bar‖ ^ 2 ≤ θ bar :=
    le_of_tendsto (((hθ.tendsto p.1).comp hxt).add
      ((hxt.sub tendsto_const_nhds).norm.pow 2))
      (Eventually.of_forall fun j => hbound (φ j))
  have he : p.1 = bar := by
    have hz : ‖p.1 - bar‖ ^ 2 = 0 := by
      have ho := hopt p.1 hrp
      nlinarith [sq_nonneg ‖p.1 - bar‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  exact ⟨p.2, hp.2, φ, hφ, he ▸ hxt, hct⟩

omit [ProperSpace E] in
theorem penalty_eventually_local_min (θ R : E → ℝ) (bar : E)
    (x : ℕ → E)
    (hm : ∀ j, IsMinOn (penalized θ R bar j) (Metric.closedBall bar 1) (x j))
    (φ : ℕ → ℕ) (ht : Tendsto (x ∘ φ) atTop (𝓝 bar)) :
    ∀ᶠ j in atTop, IsLocalMin (penalized θ R bar (φ j)) (x (φ j)) := by
  have hb : ∀ᶠ j in atTop, x (φ j) ∈ Metric.ball bar 1 :=
    ht.eventually (Metric.ball_mem_nhds bar (by norm_num))
  filter_upwards [hb] with j hj
  exact (hm (φ j)).isLocalMin (Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds hj) Metric.ball_subset_closedBall)

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/PositiveSquare.lean

open Filter Topology

namespace MangasarianFJ.GenFJ.FJFresh

theorem hasDerivAt_positive_square (x : ℝ) :
    HasDerivAt (fun t : ℝ => (max t 0) ^ 2) (2 * max x 0) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : (fun t : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] (fun t => (max t 0) ^ 2) := by
      filter_upwards [eventually_lt_nhds hx] with t ht
      simp [max_eq_right ht.le]
    simpa [max_eq_right hx.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he.symm
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    have ht : Tendsto (fun t : ℝ => max t 0) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
      have hc : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
      simpa using (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    convert ht using 1
    · ext t
      simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, sub_zero, smul_eq_mul]
      by_cases h : 0 ≤ t
      · rw [max_eq_left h]
        by_cases ht0 : t = 0
        · simp [ht0]
        · field_simp
      · simp [max_eq_right (le_of_not_ge h)]
    · simp
  · have he : (fun t : ℝ => t ^ 2) =ᶠ[𝓝 x] (fun t => (max t 0) ^ 2) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      simp [max_eq_left ht.le]
    simpa [max_eq_left hx.le] using ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq he.symm

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/GradientCalculus.lean

open scoped BigOperators InnerProductSpace

namespace MangasarianFJ.GenFJ.FJFresh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem continuous_gradient_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

theorem gradient_norm_square (bar x : E) :
    HasGradientAt (fun y : E => ‖y - bar‖ ^ 2) (2 • (x - bar)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (((hasFDerivAt_id x).sub_const bar).norm_sq).congr_fderiv (by
    ext v
    simp [InnerProductSpace.toDual_apply_apply])

theorem gradient_positive_square {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    HasGradientAt (fun y => (max (f y) 0) ^ 2)
      ((2 * max (f x) 0) • gradient f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact ((hasDerivAt_positive_square (f x)).comp_hasFDerivAt x hf.hasFDerivAt).congr_fderiv (by
    simp only [map_smul, toDual_gradient])

theorem gradient_square {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    HasGradientAt (fun y => (f y) ^ 2) ((2 * f x) • gradient f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (hf.hasFDerivAt.pow 2).congr_fderiv (by
    simp [map_smul, toDual_gradient])

theorem gradient_sum {ι : Type*} [Fintype ι] {f : ι → E → ℝ} {df : ι → E} {x : E}
    (h : ∀ i, HasGradientAt (f i) (df i) x) :
    HasGradientAt (fun y => ∑ i, f i y) (∑ i, df i) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [map_sum] using HasFDerivAt.fun_sum (fun i _ => (h i).hasFDerivAt)

theorem gradient_add {f g : E → ℝ} {df dg x : E}
    (hf : HasGradientAt f df x) (hg : HasGradientAt g dg x) :
    HasGradientAt (fun y => f y + g y) (df + dg) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (hf.hasFDerivAt.fun_add hg.hasFDerivAt).congr_fderiv (by rw [map_add])

theorem gradient_const_mul {f : E → ℝ} {df x : E} (hf : HasGradientAt f df x) (a : ℝ) :
    HasGradientAt (fun y => a * f y) (a • df) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa only [map_smul, smul_eq_mul] using hf.hasFDerivAt.const_mul a

theorem local_min_gradient_zero {f : E → ℝ} {df x : E}
    (hm : IsLocalMin f x) (hf : HasGradientAt f df x) : df = 0 := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simpa using hm.hasFDerivAt_eq_zero hf.hasFDerivAt

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/Coefficients.lean

open scoped BigOperators

namespace MangasarianFJ.GenFJ.FJFresh

abbrev Coefficients (m k : ℕ) := ℝ × ((Fin m → ℝ) × (Fin k → ℝ))

noncomputable def rawCoefficients {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) : Coefficients m k :=
  (1, (fun i => 2 * ((j : ℝ) + 1) * max (g i x) 0,
       fun l => 2 * ((j : ℝ) + 1) * h l x))

noncomputable def coeffScale {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) : ℝ :=
  ‖rawCoefficients g h j x‖⁻¹

noncomputable def normalizedCoefficients {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) : Coefficients m k :=
  coeffScale g h j x • rawCoefficients g h j x

theorem raw_norm_ge_one {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) :
    1 ≤ ‖rawCoefficients g h j x‖ := by
  calc
    1 = ‖(rawCoefficients g h j x).1‖ := by simp [rawCoefficients]
    _ ≤ ‖rawCoefficients g h j x‖ := norm_fst_le _

theorem coeffScale_bounds {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) :
    0 ≤ coeffScale g h j x ∧ coeffScale g h j x ≤ 1 := by
  unfold coeffScale
  exact ⟨inv_nonneg.mpr (norm_nonneg _), (inv_le_one₀ (by linarith [raw_norm_ge_one g h j x])).mpr (raw_norm_ge_one g h j x)⟩

theorem normalized_norm {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) :
    ‖normalizedCoefficients g h j x‖ = 1 := by
  have hn : ‖rawCoefficients g h j x‖ ≠ 0 := by linarith [raw_norm_ge_one g h j x]
  simp [normalizedCoefficients, coeffScale, norm_smul, hn]

theorem normalized_nonneg {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) :
    0 ≤ (normalizedCoefficients g h j x).1 ∧
      ∀ i, 0 ≤ (normalizedCoefficients g h j x).2.1 i := by
  have hs := (coeffScale_bounds g h j x).1
  constructor
  · simpa [normalizedCoefficients, rawCoefficients] using hs
  · intro i
    change 0 ≤ coeffScale g h j x * (2 * ((j : ℝ) + 1) * max (g i x) 0)
    positivity

theorem normalized_inactive {E : Type*} {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ) (j : ℕ) (x : E) (i : Fin m)
    (hi : g i x ≤ 0) : (normalizedCoefficients g h j x).2.1 i = 0 := by
  simp [normalizedCoefficients, rawCoefficients, max_eq_right hi]

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/PenaltyStationarity.lean

open scoped BigOperators

namespace MangasarianFJ.GenFJ.FJFresh

variable {n m k : ℕ}

theorem penalty_gradient (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hh : ∀ j, ContDiff ℝ 1 (h j)) (bar x : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    HasGradientAt (penalized θ (violation g h) bar j)
      (gradient θ x + 2 • (x-bar) +
       (∑ i, (rawCoefficients g h j x).2.1 i • gradient (g i) x) +
       ∑ l, (rawCoefficients g h j x).2.2 l • gradient (h l) x) x := by
  have ht := (hθ.differentiable one_ne_zero x).hasGradientAt
  have hgs := gradient_sum (fun i => gradient_positive_square (hg i |>.differentiable one_ne_zero x))
  have hhs := gradient_sum (fun l => gradient_square (hh l |>.differentiable one_ne_zero x))
  have hp := gradient_add (gradient_add ht (gradient_norm_square bar x))
    (gradient_const_mul (gradient_add hgs hhs) ((j : ℝ)+1))
  convert hp using 1
  · rfl
  · simp only [rawCoefficients, smul_add, Finset.smul_sum, smul_smul, ← add_assoc]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring

theorem normalized_stationarity (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hh : ∀ j, ContDiff ℝ 1 (h j)) (bar x : EuclideanSpace ℝ (Fin n)) (j : ℕ)
    (hm : IsLocalMin (penalized θ (violation g h) bar j) x) :
    (normalizedCoefficients g h j x).1 • gradient θ x +
      ∑ i, (normalizedCoefficients g h j x).2.1 i • gradient (g i) x +
      ∑ l, (normalizedCoefficients g h j x).2.2 l • gradient (h l) x =
      -(coeffScale g h j x • (2 • (x-bar))) := by
  have hz := local_min_gradient_zero hm (penalty_gradient θ g h hθ hg hh bar x j)
  have he := congrArg (fun v => coeffScale g h j x • v) hz
  simp only [smul_add, Finset.smul_sum, smul_zero] at he
  simp only [normalizedCoefficients, rawCoefficients, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, mul_one, mul_smul]
  simp only [rawCoefficients, mul_smul] at he
  apply eq_neg_of_add_eq_zero_left
  convert he using 1
  abel

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/RegularizerLimit.lean

namespace MangasarianFJ.GenFJ.FJFresh
open Filter Topology

theorem bounded_regularizer_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : ℕ → E) (bar : E) (r : ℕ → ℝ)
    (hx : Tendsto x atTop (𝓝 bar)) (hr0 : ∀ j, 0 ≤ r j) (hr1 : ∀ j, r j ≤ 1) :
    Tendsto (fun j => r j • ((2 : ℝ) • (x j - bar))) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => 2 * ‖x j - bar‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds (x := (2 : ℝ))).mul
        (hx.sub (tendsto_const_nhds (x := bar))).norm
  apply squeeze_zero_norm (fun j => ?_) ht
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr0 j)]
  norm_num only [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  exact mul_le_of_le_one_left (by positivity) (hr1 j)

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/StationarityLimit.lean

open Filter Topology
open scoped BigOperators

namespace MangasarianFJ.GenFJ.FJFresh

 theorem stationarity_limit {n m k : ℕ}
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hh : ∀ j, ContDiff ℝ 1 (h j)) (bar : EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (φ : ℕ → ℕ) (l : Coefficients m k)
    (hx : Tendsto x atTop (𝓝 bar))
    (hl : Tendsto (fun j => normalizedCoefficients g h (φ j) (x j)) atTop (𝓝 l))
    (hm : ∀ᶠ j in atTop, IsLocalMin (penalized θ (violation g h) bar (φ j)) (x j)) :
    l.1 • gradient θ bar + ∑ i, l.2.1 i • gradient (g i) bar +
      ∑ j, l.2.2 j • gradient (h j) bar = 0 := by
  have h0 := ((continuous_fst.tendsto l).comp hl).smul ((continuous_gradient_of_c1 hθ).tendsto bar |>.comp hx)
  have h1 : Tendsto (fun j => ∑ i, (normalizedCoefficients g h (φ j) (x j)).2.1 i •
      gradient (g i) (x j)) atTop (𝓝 (∑ i, l.2.1 i • gradient (g i) bar)) := by
    apply tendsto_finsetSum
    intro i _
    exact (((continuous_apply i).tendsto l.2.1).comp (((continuous_fst.comp continuous_snd).tendsto l).comp hl)).smul
      ((continuous_gradient_of_c1 (hg i)).tendsto bar |>.comp hx)
  have h2 : Tendsto (fun j => ∑ i, (normalizedCoefficients g h (φ j) (x j)).2.2 i •
      gradient (h i) (x j)) atTop (𝓝 (∑ i, l.2.2 i • gradient (h i) bar)) := by
    apply tendsto_finsetSum
    intro i _
    exact (((continuous_apply i).tendsto l.2.2).comp (((continuous_snd.comp continuous_snd).tendsto l).comp hl)).smul
      ((continuous_gradient_of_c1 (hh i)).tendsto bar |>.comp hx)
  have hr := bounded_regularizer_tendsto x bar (fun j => coeffScale g h (φ j) (x j)) hx
    (fun j => (coeffScale_bounds g h (φ j) (x j)).1)
    (fun j => (coeffScale_bounds g h (φ j) (x j)).2)
  have he : (fun j => (normalizedCoefficients g h (φ j) (x j)).1 • gradient θ (x j) +
      ∑ i, (normalizedCoefficients g h (φ j) (x j)).2.1 i • gradient (g i) (x j) +
      ∑ i, (normalizedCoefficients g h (φ j) (x j)).2.2 i • gradient (h i) (x j))
      =ᶠ[atTop] fun j => -(coeffScale g h (φ j) (x j) • ((2 : ℝ) • (x j-bar))) := by
    filter_upwards [hm] with j hj
    simpa only [two_smul] using normalized_stationarity θ g h hθ hg hh bar (x j) (φ j) hj
  exact tendsto_nhds_unique ((h0.add h1).add h2) (by simpa using hr.neg.congr' he.symm)

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/CoefficientLimits.lean

namespace MangasarianFJ.GenFJ.FJFresh
open Filter Topology

 theorem coefficient_limit_conditions {E : Type*} [TopologicalSpace E] {m k : ℕ}
    (g : Fin m → E → ℝ) (h : Fin k → E → ℝ)
    (bar : E) (x : ℕ → E) (φ : ℕ → ℕ) (l : Coefficients m k)
    (hg : ∀ i, Continuous (g i)) (hfeas : ∀ i, g i bar ≤ 0)
    (hx : Tendsto x atTop (𝓝 bar))
    (hc : Tendsto (fun j => normalizedCoefficients g h (φ j) (x j)) atTop (𝓝 l)) :
    0 ≤ l.1 ∧ (∀ i, 0 ≤ l.2.1 i) ∧ ∑ i, l.2.1 i * g i bar = 0 := by
  have h0 : 0 ≤ l.1 := ge_of_tendsto ((continuous_fst.tendsto l).comp hc)
    (Eventually.of_forall fun j => (normalized_nonneg g h (φ j) (x j)).1)
  have hi : ∀ i, Tendsto (fun j => (normalizedCoefficients g h (φ j) (x j)).2.1 i)
      atTop (𝓝 (l.2.1 i)) := fun i => tendsto_pi_nhds.mp ((continuous_fst.tendsto l.2).comp
    ((continuous_snd.tendsto l).comp hc)) i
  refine ⟨h0, fun i => ge_of_tendsto (hi i)
    (Eventually.of_forall fun j => (normalized_nonneg g h (φ j) (x j)).2 i), ?_⟩
  apply Finset.sum_eq_zero
  intro i _
  by_cases hz : g i bar = 0
  · simp only [hz, mul_zero]
  · have hn : g i bar < 0 := lt_of_le_of_ne (hfeas i) hz
    have he : ∀ᶠ j in atTop, (normalizedCoefficients g h (φ j) (x j)).2.1 i = 0 := by
      have hgx := ((hg i).tendsto bar).comp hx
      filter_upwards [hgx.eventually (isOpen_Iio.mem_nhds hn)] with j hj
      exact normalized_inactive g h (φ j) (x j) i (le_of_lt hj)
    have hl : l.2.1 i = 0 := tendsto_nhds_unique (hi i)
      (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm))
    simp only [hl, zero_mul]

theorem coefficients_nontrivial {m k : ℕ} (l : Coefficients m k) (hl : ‖l‖ = 1) :
    l.1 ≠ 0 ∨ (∃ i, l.2.1 i ≠ 0) ∨ ∃ j, l.2.2 j ≠ 0 := by
  by_contra hn
  push Not at hn
  have he : l = 0 := by
    apply Prod.ext hn.1
    exact Prod.ext (funext hn.2.1) (funext hn.2.2)
  rw [he, norm_zero] at hl
  norm_num at hl

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/NativeConclusion.lean

open Filter Topology
namespace MangasarianFJ.GenFJ.FJFresh

theorem native_generalized_fritz_john {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hh : ∀ j, ContDiff ℝ 1 (h j))
    (xbar : EuclideanSpace ℝ (Fin n)) (hsol : IsSolution θ g h xbar) :
    ∃ (u0 : ℝ) (u : Fin m → ℝ) (v : Fin k → ℝ),
      u0 • gradient θ xbar + ∑ i, u i • gradient (g i) xbar
          + ∑ j, v j • gradient (h j) xbar = 0 ∧
      ∑ i, u i * g i xbar = 0 ∧
      0 ≤ u0 ∧ (∀ i, 0 ≤ u i) ∧
      (u0 ≠ 0 ∨ (∃ i, u i ≠ 0) ∨ ∃ j, v j ≠ 0) := by
  have hR := continuous_violation (fun i => (hg i).continuous) (fun j => (hh j).continuous)
  have hRbar : violation g h xbar = 0 := (violation_eq_zero_iff g h xbar).mpr hsol.1
  obtain ⟨x, hx⟩ := exists_penalty_minimizers θ (violation g h) xbar hθ.continuous hR
  let K : Set (Coefficients m k) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere 0 1
  have hc : ∀ j, normalizedCoefficients g h j (x j) ∈ K := by
    intro j
    simpa [K, Metric.mem_sphere, dist_zero_right] using normalized_norm g h j (x j)
  obtain ⟨l, hl, φ, _hφ, hxt, hct⟩ := penalty_product_subsequence θ (violation g h) xbar
    hθ.continuous hR (violation_nonneg g h) hRbar
    (fun z hz => hsol.2 z ((violation_eq_zero_iff g h z).mp hz))
    x (fun j => (hx j).1) (fun j => (hx j).2) K hK
    (fun j => normalizedCoefficients g h j (x j)) hc
  have hlocal := penalty_eventually_local_min θ (violation g h) xbar x
    (fun j => (hx j).2) φ hxt
  have hs := stationarity_limit θ g h hθ hg hh xbar (x ∘ φ) φ l hxt hct hlocal
  obtain ⟨h0, hi, hcomp⟩ := coefficient_limit_conditions g h xbar (x ∘ φ) φ l
    (fun i => (hg i).continuous) hsol.1.1 hxt hct
  have hnorm : ‖l‖ = 1 := by simpa [K, Metric.mem_sphere, dist_zero_right] using hl
  exact ⟨l.1, l.2.1, l.2.2, hs, hcomp, h0, hi, coefficients_nontrivial l hnorm⟩

end MangasarianFJ.GenFJ.FJFresh

-- Complete module: FJProof/FinalRoot.lean

namespace MangasarianFJ.GenFJ
theorem generalized_fritz_john {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hh : ∀ j, ContDiff ℝ 1 (h j))
    (xbar : EuclideanSpace ℝ (Fin n)) (hsol : IsSolution θ g h xbar) :
    ∃ (u0 : ℝ) (u : Fin m → ℝ) (v : Fin k → ℝ),
      u0 • gradient θ xbar + ∑ i, u i • gradient (g i) xbar
          + ∑ j, v j • gradient (h j) xbar = 0 ∧
      ∑ i, u i * g i xbar = 0 ∧
      0 ≤ u0 ∧ (∀ i, 0 ≤ u i) ∧
      (u0 ≠ 0 ∨ (∃ i, u i ≠ 0) ∨ ∃ j, v j ≠ 0) := by
  exact FJFresh.native_generalized_fritz_john θ g h hθ hg hh xbar hsol
end MangasarianFJ.GenFJ

open MangasarianFJ.GenFJ

theorem solution {n m k : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin n) → ℝ)
    (hθ : ContDiff ℝ 1 θ) (hg : ∀ i, ContDiff ℝ 1 (g i)) (hh : ∀ j, ContDiff ℝ 1 (h j))
    (xbar : EuclideanSpace ℝ (Fin n)) (hsol : IsSolution θ g h xbar) :
    ∃ (u0 : ℝ) (u : Fin m → ℝ) (v : Fin k → ℝ),
      u0 • gradient θ xbar + ∑ i, u i • gradient (g i) xbar
          + ∑ j, v j • gradient (h j) xbar = 0 ∧
      ∑ i, u i * g i xbar = 0 ∧
      0 ≤ u0 ∧ (∀ i, 0 ≤ u i) ∧
      (u0 ≠ 0 ∨ (∃ i, u i ≠ 0) ∨ ∃ j, v j ≠ 0) := by
  exact MangasarianFJ.GenFJ.generalized_fritz_john θ g h hθ hg hh xbar hsol
