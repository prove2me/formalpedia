-- Prove2me | solution 1 for GlobalTheory.expSeries_contDiff_and_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:48:35.314214+00:00
-- url     : https://prove2.me/submissions/6f33da24-4cb3-4e28-9b8d-8b1abda9d55e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExpSeriesContDiffAndHasDerivAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped ContDiff
namespace GlobalTheory
section ExpSeries
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type}
end ExpSeries
open scoped ContDiff in
private lemma norm_smulRight_le_opNorm_mul_norm {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (L : V →L[ℝ] ℂ) (w : E) :
    ‖L.smulRight w‖ ≤ ‖L‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖L h‖ * ‖w‖ ≤ ‖L‖ * ‖h‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm h) (norm_nonneg _)
    _ = ‖L‖ * ‖w‖ * ‖h‖ := by ring
open scoped ContDiff in
private lemma mul_exp_mul_le_exp_add_one_mul (r R : ℝ) :
    r * Real.exp (R * r) ≤ Real.exp ((R + 1) * r) := by
  calc r * Real.exp (R * r) ≤ Real.exp r * Real.exp (R * r) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp r]) (Real.exp_pos _).le
    _ = Real.exp ((R + 1) * r) := by rw [← Real.exp_add]; ring_nf
open scoped ContDiff in
private lemma summable_norm_smulRight_mul_exp {V E I : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (R : ℝ) :
    Summable fun i => ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hw (R + 1))
  calc ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖)
      ≤ ‖m i‖ * ‖w i‖ * Real.exp (R * ‖m i‖) :=
        mul_le_mul_of_nonneg_right (norm_smulRight_le_opNorm_mul_norm _ _) (Real.exp_pos _).le
    _ = ‖w i‖ * (‖m i‖ * Real.exp (R * ‖m i‖)) := by ring
    _ ≤ ‖w i‖ * Real.exp ((R + 1) * ‖m i‖) :=
        mul_le_mul_of_nonneg_left (mul_exp_mul_le_exp_add_one_mul _ _) (norm_nonneg _)
open scoped ContDiff in
private lemma norm_cexp_le_exp_mul_opNorm_of_norm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {y : V} {r : ℝ} (hy : ‖y‖ ≤ r) :
    ‖Complex.exp (L y)‖ ≤ Real.exp (r * ‖L‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  calc (L y).re ≤ ‖L y‖ := Complex.re_le_norm _
    _ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
    _ ≤ r * ‖L‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
open scoped ContDiff in
private lemma hasFDerivAt_tsum_cexp_smul_of_summable_exp {V E I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (x : V) :
    HasFDerivAt (fun v => ∑' i, Complex.exp (m i v) • w i)
      (∑' i, Complex.exp (m i x) • (m i).smulRight (w i)) x := by
  set r := ‖x‖ + 1
  have hx : x ∈ Metric.ball (0 : V) r := by rw [mem_ball_zero_iff]; simp [r]
  refine hasFDerivAt_tsum_of_isPreconnected (u := fun i => ‖(m i).smulRight (w i)‖ *
      Real.exp (r * ‖m i‖)) (f := fun i v => Complex.exp (m i v) • w i)
    (f' := fun i y => Complex.exp (m i y) • (m i).smulRight (w i))
    (summable_norm_smulRight_mul_exp m w hw r) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ hx ?_ hx
  · intro i y _
    refine (((m i).hasFDerivAt.cexp).smul_const (w i)).congr_fderiv ?_
    ext h
    simp [smul_smul]
  · intro i y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by rw [mem_ball_zero_iff] at hy; exact hy.le)) (norm_nonneg _)
  · refine Summable.of_norm_bounded (hw r) fun i => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by simp [r])) (norm_nonneg _)
open scoped ContDiff in
private lemma contDiff_tsum_cexp_smul_of_summable_exp {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : I → V →L[ℝ] ℂ) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (w : I → E),
      (∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ n (fun v => ∑' i, Complex.exp (m i v) • w i) := by
  induction n with
  | zero =>
    intro E _ _ _ w hw
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x).continuousAt)
  | succ n ih =>
    intro E _ _ _ w hw
    have hd := fun x => hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x
    push_cast
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd x).differentiableAt, fun h => by simp at h, ?_⟩
    have hfd : fderiv ℝ (fun v => ∑' i, Complex.exp (m i v) • w i) =
        fun x => ∑' i, Complex.exp (m i x) • (m i).smulRight (w i) :=
      funext fun x => (hd x).fderiv
    rw [hfd]
    exact ih (V →L[ℝ] E) (fun i => (m i).smulRight (w i))
      (summable_norm_smulRight_mul_exp m w hw)
end GlobalTheory
end

set_option autoImplicit false
open scoped ContDiff
open GlobalTheory
open scoped ContDiff
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) (c : I → ℂ)
      (m : I → V →L[ℝ] ℂ), (∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ ∞ (fun v : V => ∑' i, c i * Complex.exp (m i v)) ∧
        ∀ z : V, Summable (fun i => c i * m i z) ∧
          HasDerivAt (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z)))
            (∑' i, c i * m i z) 0 := by
  intro V _ _ I c m hc
  have hfun : (fun v : V => ∑' i, c i * Complex.exp (m i v)) =
      fun v => ∑' i, Complex.exp (m i v) • c i :=
    funext fun v => tsum_congr fun i => by rw [smul_eq_mul, mul_comm]
  have hz : ∀ z : V, Summable fun i => c i * m i z := by
    intro z
    refine Summable.of_norm_bounded ((hc 1).mul_left ‖z‖) fun i => ?_
    rw [norm_mul, one_mul]
    have h1 : 0 ≤ ‖c i‖ * ‖z‖ * (Real.exp ‖m i‖ - ‖m i‖) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by linarith [Real.add_one_le_exp ‖m i‖])
    have h2 : ‖c i‖ * ‖m i z‖ ≤ ‖c i‖ * (‖m i‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((m i).le_opNorm z) (norm_nonneg _)
    nlinarith
  refine ⟨?_, fun z => ⟨hz z, ?_⟩⟩
  · rw [hfun]
    exact contDiff_infty.2 fun n => contDiff_tsum_cexp_smul_of_summable_exp m n ℂ c hc
  · have hF := hasFDerivAt_tsum_cexp_smul_of_summable_exp m c hc (0 : V)
    have hl := (hasDerivAt_id (0 : ℝ)).smul_const z
    have h := hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (zero_smul ℝ z).symm
    have hS : Summable fun i => (m i).smulRight (c i) := by
      refine Summable.of_norm ?_
      simpa using summable_norm_smulRight_mul_exp m c hc 0
    have hS' : Summable fun i => Complex.exp (m i 0) • (m i).smulRight (c i) := by
      simpa using hS
    have hfeq : (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z))) =
        ((fun v => ∑' i, Complex.exp (m i v) • c i) ∘ fun y => id y • z) :=
      funext fun t => tsum_congr fun i => by simp [mul_comm]
    rw [hfeq]
    refine h.congr_deriv ?_
    have happ := (hS'.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ) • z))).tsum_eq
    simp only [ContinuousLinearMap.apply_apply] at happ
    rw [← happ]
    exact tsum_congr fun i => by simp [mul_comm]
end _root_.GlobalTheory
end GlobalTheory
