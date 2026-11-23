-- Prove2me | solution 1 for NoHair.translated_ball_source_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:25:22.370474+00:00
-- url     : https://prove2.me/submissions/c923e552-660a-4941-bc4b-e0555deb1c91

import Definitions.Def_NoHair_staticInvertedEndMetric
import Mathlib.Analysis.InnerProductSpace.Laplacian
open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped ContDiff Topology

private abbrev X := ADMPoint
private lemma ball_real (x : X) {r : ℝ} (hr : 0<r) :
    volume.real (ball x r)=r^3*volume.real (ball (0:X) 1) := by
  rw [measureReal_def,volume.addHaar_ball_of_pos x hr,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
  simp [measureReal_def,finrank_euclideanSpace]

theorem solution (q : ADMPoint → ℝ) (hi : Integrable q)
    (hd : ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ z : ADMPoint, R < ‖z‖ → |q z| ≤ C/‖z‖^4) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧ ∀ x : ADMPoint, R < ‖x‖ → ∀ t : ℝ, 0 < t →
      |(∫ z in ball x (t*‖x‖), q z)/t^2| ≤ K/(t+1)^2 := by
  obtain ⟨S,C,hS,hC,hdec⟩:=hd
  let V:=volume.real (ball (0:X) 1)
  let Q:=∫ z, |q z|
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hQ : 0 ≤ Q := integral_nonneg (fun z => abs_nonneg _)
  let K:=64*C*V+9*Q+1
  let R:=max 1 (2*S)
  have hK : 0<K := by dsimp [K]; positivity
  have hR : 0<R := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨K,R,hK,hR,?_⟩
  intro x hx t ht
  let r:=‖x‖
  have hr : 1≤r := (le_max_left _ _).trans hx.le
  have hrp : 0<r := zero_lt_one.trans_le hr
  have hrs : 2*S<r := (le_max_right _ _).trans_lt hx
  let M:=∫ z in ball x (t*r),q z
  change |M/t^2| ≤ K/(t+1)^2
  rw [abs_div,abs_of_pos (sq_pos_of_pos ht),div_le_div_iff₀ (sq_pos_of_pos ht) (by positivity)]
  by_cases hsmall : t ≤ 1/2
  · have hb (z : X) (hz : z∈ball x (t*r)) : ‖q z‖ ≤ 16*C/r^4 := by
      have hdist := Metric.mem_ball.mp hz
      have htri : r ≤ dist z x+‖z‖ := by
        simpa [r,dist_comm x z] using dist_triangle x z 0
      have hz' : r/2 ≤ ‖z‖ := by nlinarith only [htri,hdist,mul_nonneg (sub_nonneg.mpr hsmall) hrp.le]
      apply (hdec z (by linarith)).trans
      apply (div_le_div_iff₀ (pow_pos (by linarith : 0<‖z‖) 4) (pow_pos hrp 4)).2
      have e:=pow_le_pow_left₀ (by positivity : 0≤r/2) hz' 4
      nlinarith only [mul_nonneg hC.le (sub_nonneg.mpr e)]
    have bnd : |M| ≤ 16*C/r^4 *((t*r)^3*V) := by
      exact (norm_setIntegral_le_of_norm_le_const (measure_ball_lt_top (μ:=volume) (x:=x) (r:=t*r)) hb).trans_eq
        (congrArg (fun z => 16*C/r^4*z) (ball_real x (mul_pos ht hrp)))
    have alg : 16*C/r^4*((t*r)^3*V)=(16*C*V*t^3)/r := by field_simp [hrp.ne'] <;> ring
    rw [alg] at bnd
    have bm : |M| ≤ 16*C*V*t^3 := bnd.trans (div_le_self (by positivity) hr)
    have bt : (t+1)^2≤4 := by nlinarith only [mul_nonneg (by linarith : 0≤1-t) (by linarith : 0≤3+t)]
    have tt : t^3 ≤ t^2 := by nlinarith only [mul_nonneg (sq_nonneg t) (by linarith : 0≤1-t)]
    calc
      _ ≤ (16*C*V*t^3)*4 := mul_le_mul bm bt (sq_nonneg _) (by positivity)
      _ ≤ (64*C*V)*t^2 := by nlinarith only [mul_nonneg (by positivity : 0≤64*C*V) (sub_nonneg.mpr tt)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (sq_nonneg _)
  · have bm : |M| ≤ Q := (norm_integral_le_integral_norm _).trans
        (setIntegral_le_integral hi.norm (ae_of_all _ (fun _ => norm_nonneg _)))
    have bt : (t+1)^2 ≤ 9*t^2 := by
      nlinarith only [mul_nonneg (by linarith : 0≤2*t-1) (by linarith : 0≤4*t+1)]
    calc
      _ ≤ Q*(9*t^2) := mul_le_mul bm bt (sq_nonneg _) hQ
      _ ≤ K*t^2 := by
        have e : 9*Q ≤ K := by
          dsimp [K]
          have hcv : 0≤64*C*V := by positivity
          linarith only [hcv]
        nlinarith only [mul_nonneg (sub_nonneg.mpr e) (sq_nonneg t)]
