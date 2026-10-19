-- Prove2me | solution 1 for OAI.NoiselessRegression.capWeight_mass_mixed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:54:26.291395+00:00
-- url     : https://prove2.me/submissions/2217e7dd-eea9-4e0d-bc21-738aab8bf011

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
open scoped Pointwise

omit [Nontrivial E] in
theorem nr_sphereLaw_le_one (B : Set E) : ambientSphereLaw (E := E) B ≤ 1 := by
  unfold ambientSphereLaw sphereLaw
  calc _ ≤ ((((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere).map Subtype.val) univ :=
        measure_mono (Set.subset_univ _)
    _ = ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure E).toSphere univ := by
        rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]; rfl
    _ ≤ 1 := ENNReal.inv_mul_le_one _

theorem nr_cap_small (c : E) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ambientSphereLaw (E := E) (Metric.closedBall c ρ) ≤
      ENNReal.ofReal (2^Module.finrank ℝ E * ρ^(Module.finrank ℝ E - 1)) := by
  set n := Module.finrank ℝ E with hn
  have hn1 : 1 ≤ n := Module.finrank_pos
  set μ := (volume : Measure E)
  let A : Set (Metric.sphere (0:E) 1) := Subtype.val ⁻¹' Metric.closedBall c ρ
  have hA : MeasurableSet A := measurable_subtype_coe measurableSet_closedBall
  let C : Set E := Set.Ioo (0:ℝ) 1 • (Subtype.val '' A)
  have h1 : ambientSphereLaw (E := E) (Metric.closedBall c ρ) =
      (μ.toSphere univ)⁻¹ * μ.toSphere A := by
    unfold ambientSphereLaw sphereLaw
    rw [Measure.map_apply measurable_subtype_coe measurableSet_closedBall]; rfl
  rw [h1, Measure.toSphere_apply' μ hA, Measure.toSphere_apply_univ]
  set B := μ (Metric.ball (0:E) 1)
  have hB0 : B ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  have hCB : C ⊆ Metric.ball (0:E) 1 := by
    rintro _ ⟨s, hs, _, ⟨x, hx, rfl⟩, rfl⟩
    have hx1 : ‖(x:E)‖ = 1 := by simp
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, hx1, mul_one, Real.norm_eq_abs,
      abs_of_pos hs.1]
    exact hs.2
  have hCt : μ C ≠ ⊤ := ne_top_of_le_ne_top hBt (measure_mono hCB)
  set l := 1 - ρ with hl
  have hl0 : 0 < l := by linarith
  have hsub : C ⊆ l • C ∪ Metric.closedBall c (2*ρ) := by
    rintro _ ⟨s, hs, _, ⟨x, hx, rfl⟩, rfl⟩
    have hx1 : ‖(x:E)‖ = 1 := by simp
    have hxc : dist (x:E) c ≤ ρ := hx
    by_cases hsl : s < l
    · left
      refine ⟨(s/l) • (x:E), ⟨s/l, ⟨div_pos hs.1 hl0, (div_lt_one hl0).mpr hsl⟩, (x:E), ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      show l • ((s/l) • (x:E)) = s • (x:E)
      rw [smul_smul, mul_div_cancel₀ _ hl0.ne']
    · right
      push Not at hsl
      rw [Metric.mem_closedBall]
      calc dist (s • (x:E)) c ≤ dist (s • (x:E)) (x:E) + dist (x:E) c := dist_triangle _ _ _
        _ ≤ ρ + ρ := by
          gcongr
          rw [dist_eq_norm, show s • (x:E) - (x:E) = (s - 1) • (x:E) by rw [sub_smul, one_smul],
            norm_smul, hx1, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith [hs.2])]
          linarith
        _ = 2*ρ := by ring
  have hmeas : μ C ≤ ENNReal.ofReal (l^n) * μ C + ENNReal.ofReal ((2*ρ)^n) * B := by
    calc μ C ≤ μ (l • C ∪ Metric.closedBall c (2*ρ)) := measure_mono hsub
      _ ≤ μ (l • C) + μ (Metric.closedBall c (2*ρ)) := measure_union_le _ _
      _ = _ := by
        rw [Measure.addHaar_smul, Measure.addHaar_closedBall μ c (by linarith),
          abs_of_nonneg (pow_nonneg hl0.le _)]
  have hreal : (μ C).toReal ≤ l^n * (μ C).toReal + (2*ρ)^n * B.toReal := by
    have := ENNReal.toReal_mono (by finiteness) hmeas
    rwa [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hl0.le _), ENNReal.toReal_ofReal (by positivity)] at this
  have hln : l^n ≤ l := pow_le_of_le_one hl0.le (by linarith) (by omega)
  have hX0 : 0 ≤ (μ C).toReal := ENNReal.toReal_nonneg
  have hpow : (2*ρ)^n = 2^n * ρ^(n-1) * ρ := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hn1]
  have hkey : (μ C).toReal ≤ 2^n * ρ^(n-1) * B.toReal := by
    have hB0' : 0 ≤ B.toReal := ENNReal.toReal_nonneg
    have : ρ * (μ C).toReal ≤ ρ * (2^n * ρ^(n-1) * B.toReal) := by nlinarith
    exact le_of_mul_le_mul_left this hρ
  have hCle : μ C ≤ ENNReal.ofReal (2^n * ρ^(n-1)) * B := by
    rw [← ENNReal.ofReal_toReal hCt, ← ENNReal.ofReal_toReal hBt, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hkey
  have hn0 : ((n:ℕ):ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change ((n:ℝ≥0∞) * B)⁻¹ * ((n:ℝ≥0∞) * μ C) ≤ _
  calc ((n:ℝ≥0∞) * B)⁻¹ * ((n:ℝ≥0∞) * μ C)
      ≤ ((n:ℝ≥0∞) * B)⁻¹ * ((n:ℝ≥0∞) * (ENNReal.ofReal (2^n * ρ^(n-1)) * B)) := by gcongr
    _ = ENNReal.ofReal (2^n * ρ^(n-1)) * (((n:ℝ≥0∞) * B)⁻¹ * ((n:ℝ≥0∞) * B)) := by ring
    _ = ENNReal.ofReal (2^n * ρ^(n-1)) := by
        rw [ENNReal.inv_mul_cancel (mul_ne_zero hn0 hB0) (ENNReal.mul_ne_top (by simp) hBt), mul_one]

theorem nr_cap (c : E) {ρ : ℝ} (hρ : 0 < ρ) :
    ambientSphereLaw (E := E) (Metric.closedBall c ρ) ≤
      ENNReal.ofReal (2^Module.finrank ℝ E * ρ^(Module.finrank ℝ E - 1)) := by
  rcases lt_or_ge ρ 1 with h | h
  · exact nr_cap_small c hρ h
  · refine (nr_sphereLaw_le_one _).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1:ℝ) ≤ 2^Module.finrank ℝ E := one_le_pow₀ (by norm_num)
    have h2 : (1:ℝ) ≤ ρ^(Module.finrank ℝ E - 1) := one_le_pow₀ h
    nlinarith

theorem solution (y : E) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a : ℕ) {b : ℝ} (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ)) :
    PolynomialMass ((ambientSphereLaw (E := E)).withDensity (capWeight y ε)) a
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) := by
  intro z r hr
  rw [show capWeight y ε = (Metric.closedBall y ε).indicator 1 from rfl,
    withDensity_indicator_one measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall]
  set n := Module.finrank ℝ E
  set m := min r ε with hm
  have hm0 : 0 < m := lt_min hr hε
  have hm1 : m ≤ 1 := (min_le_right _ _).trans hε1
  have hcap : ambientSphereLaw (E := E) (Metric.closedBall z r ∩ Metric.closedBall y ε) ≤
      ENNReal.ofReal (2^n * m^(n-1)) := by
    rcases le_total r ε with h | h
    · have : m = r := min_eq_left h
      rw [this]
      exact (measure_mono Set.inter_subset_left).trans (nr_cap z hr)
    · have : m = ε := min_eq_right h
      rw [this]
      exact (measure_mono Set.inter_subset_right).trans (nr_cap y hε)
  refine hcap.trans ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : m^(n-1) ≤ m^((a:ℝ)+b) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hm0 hm1 (by exact_mod_cast hab)
  have h2 : m^((a:ℝ)+b) = m^a * m^b := by
    rw [Real.rpow_add hm0, Real.rpow_natCast]
  have h3 : m^a ≤ r^a := pow_le_pow_left₀ hm0.le (min_le_left _ _) _
  have h4 : m^b ≤ ε^b := Real.rpow_le_rpow hm0.le (min_le_right _ _) hb
  have h5 : (2:ℝ)^n ≤ 3*4^n := by
    have : (2:ℝ)^n ≤ 4^n := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    nlinarith [pow_pos (show (0:ℝ) < 4 by norm_num) n]
  have hmb : 0 ≤ m^b := Real.rpow_nonneg hm0.le _
  have hma : 0 ≤ m^a := pow_nonneg hm0.le _
  calc (2:ℝ)^n * m^(n-1) ≤ 2^n * (m^a * m^b) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (3*4^n) * (r^a * ε^b) := by
        apply mul_le_mul h5 (mul_le_mul h3 h4 hmb (pow_nonneg hr.le _)) (by positivity) (by positivity)
    _ = 3*4^n * ε^b * r^a := by ring

