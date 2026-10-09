-- Prove2me | solution 1 for MeasureTheory.average_covector_flux_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T09:40:11.210688+00:00
-- url     : https://prove2.me/submissions/1f70551c-9607-4f48-852a-829e7411d84f

import Theorems.Thm_MeasureTheory_integral_directional_derivative_ball
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set

theorem solution {n : ℕ} (hn : 0 < n)
    {A : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hA : ∀ y ∈ Metric.closedBall x r, ContDiffAt ℝ 1 A y) :
    (⨍ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      A (x + r • ω.1) ω.1 ∂(volume.toSphere)) =
      (r / (n : ℝ)) *
        (⨍ y in Metric.ball x r,
          ∑ i : Fin n, fderiv ℝ A y (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let f (i : Fin n) (y : E) := A y (e i)
  let d (i : Fin n) (y : E) := fderiv ℝ A y (e i) (e i)
  let b (i : Fin n) (ω : S) := f i (x + r • ω.1) * inner ℝ (e i) ω.1
  have hf (i : Fin n) (y : E) (hy : y ∈ Metric.closedBall x r) :
      ContDiffAt ℝ 1 (f i) y := (hA y hy).clm_apply contDiffAt_const
  have hd (i : Fin n) (y : E) (hy : y ∈ Metric.closedBall x r) :
      fderiv ℝ (f i) y (e i) = d i y := by
    dsimp [f, d]
    rw [fderiv_clm_apply ((hA y hy).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp
  have hdi (i : Fin n) : IntegrableOn (d i) (Metric.ball x r) := by
    have hc : ContinuousOn (d i) (Metric.closedBall x r) := by
      intro y hy
      exact (((hA y hy).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
        |>.clm_apply continuousAt_const).continuousWithinAt
    exact (hc.integrableOn_compact (isCompact_closedBall x r)).mono_set
      Metric.ball_subset_closedBall
  have hp (ω : S) : x + r • ω.1 ∈ Metric.closedBall x r := by
    have hω : ‖ω.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using ω.property
    simp [Metric.mem_closedBall, dist_eq_norm, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hω]
  have hbi (i : Fin n) : Integrable (b i) (volume.toSphere : Measure S) := by
    have hc : Continuous (b i) := by
      rw [continuous_iff_continuousAt]
      intro ω
      have hc : ContinuousAt (fun w : S => x + r • w.1) ω := by fun_prop
      have hfc : ContinuousAt (fun w : S => f i (x + r • w.1)) ω :=
        (hf i _ (hp ω)).continuousAt.comp (f := fun w : S => x + r • w.1) hc
      exact hfc.mul (by fun_prop)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi (i : Fin n) :
      (∫ y in Metric.ball x r, d i y) = r ^ (n - 1) * ∫ ω : S, b i ω ∂volume.toSphere := by
    have h := integral_directional_derivative_ball hn hr (hf i) (e i)
    rw [← h]
    exact setIntegral_congr_fun measurableSet_ball fun y hy => (hd i y
      (Metric.ball_subset_closedBall hy)).symm
  have hb (ω : S) : (∑ i : Fin n, b i ω) = A (x + r • ω.1) ω.1 := by
    have he := e.sum_repr' ω.1
    apply_fun (A (x + r • ω.1)) at he
    simpa [b, f, map_sum, map_smul, smul_eq_mul, mul_comm] using he
  have hsum :
      (∫ y in Metric.ball x r, ∑ i : Fin n, d i y) =
        r ^ (n - 1) * ∫ ω : S, A (x + r • ω.1) ω.1 ∂volume.toSphere := by
    rw [integral_finsetSum _ (fun i _ => hdi i)]
    calc
      (∑ i : Fin n, ∫ y in Metric.ball x r, d i y) =
          ∑ i : Fin n, r ^ (n - 1) * ∫ ω : S, b i ω ∂volume.toSphere :=
        Finset.sum_congr rfl (fun i _ => hi i)
      _ = _ := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hbi i)]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall hb)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmass : (volume.toSphere : Measure S).real univ =
      (n : ℝ) * (volume : Measure E).real (Metric.ball 0 1) := by
    simp [S, E]
  have hvol : (volume : Measure E).real (Metric.ball x r) =
      r ^ n * (volume : Measure E).real (Metric.ball 0 1) := by
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp [E, measureReal_def]
  have hu : (volume : Measure E).real (Metric.ball 0 1) ≠ 0 := by
    rw [measureReal_ne_zero_iff (measure_ball_lt_top.ne)]
    exact (Metric.measure_ball_pos volume (0 : E) zero_lt_one).ne'
  have hpow : r ^ n = r * r ^ (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [pow_succ, mul_comm]
  change (⨍ ω : S, A (x + r • ω.1) ω.1 ∂volume.toSphere) =
    (r / (n : ℝ)) * (⨍ y in Metric.ball x r, ∑ i : Fin n, d i y)
  rw [average_eq, setAverage_eq, hmass, hvol, hsum]
  simp only [smul_eq_mul]
  rw [hpow]
  field_simp [hnR, hu, hr.ne']
  <;> ring
