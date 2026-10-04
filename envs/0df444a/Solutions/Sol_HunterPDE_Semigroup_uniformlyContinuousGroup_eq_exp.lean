-- Prove2me | solution 1 for HunterPDE.Semigroup.uniformlyContinuousGroup_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:55:32.157242+00:00
-- url     : https://prove2.me/submissions/ff73c338-9de2-46f8-a489-5001e792eea6

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup

open scoped ContDiff
open Filter Topology MeasureTheory

namespace UCGAux

section Aux

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

noncomputable local instance instNormedAlgebraReal : NormedAlgebra ℝ (X →L[𝕜] X) where
  norm_smul_le := norm_smul_le

noncomputable local instance instNormedAlgebraRat : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- A uniformly continuous group is continuous. -/
lemma continuous_T {T : ℝ → X →L[𝕜] X} (hT : HunterPDE.Semigroup.IsUniformlyContinuousGroup T) :
    Continuous T := by
  obtain ⟨h0, hmul, hlim⟩ := hT
  rw [continuous_iff_continuousAt]
  intro t
  have hfun : T = fun u => T t * T (u - t) := by
    funext u; rw [hmul, add_sub_cancel]
  have h1 : Tendsto (fun u : ℝ => u - t) (𝓝 t) (𝓝 0) := by
    exact tendsto_sub_nhds_zero_iff.2 tendsto_id
  have h2 : Tendsto (fun u => T t * T (u - t)) (𝓝 t) (𝓝 (T t * 1)) :=
    tendsto_const_nhds.mul (hlim.comp h1)
  rw [mul_one] at h2
  exact h2.congr (fun u => (congrFun hfun u).symm)

/-- For small `s > 0` the integral `∫₀^s T` is invertible. -/
lemma exists_unit {T : ℝ → X →L[𝕜] X} (hT : HunterPDE.Semigroup.IsUniformlyContinuousGroup T) :
    ∃ s : ℝ, 0 < s ∧ IsUnit (∫ τ in (0 : ℝ)..s, T τ) := by
  have hc := continuous_T hT
  have hlim := hT.2.2
  obtain ⟨ε, hε, hball⟩ := Metric.tendsto_nhds_nhds.1 hlim (1 / 2) (by norm_num)
  refine ⟨ε / 2, by positivity, ?_⟩
  set s := ε / 2 with hs
  have hs0 : 0 < s := by positivity
  have hint : IntervalIntegrable T volume 0 s := hc.intervalIntegrable _ _
  have hsplit : ∫ τ in (0 : ℝ)..s, T τ =
      s • (1 : X →L[𝕜] X) + ∫ τ in (0 : ℝ)..s, (T τ - 1) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  have hnorm : ‖∫ τ in (0 : ℝ)..s, (T τ - 1)‖ ≤ (1 / 2) * s := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
      (f := fun τ => T τ - 1) (C := 1 / 2) (fun x hx => ?_)
    · simpa [abs_of_pos hs0] using this
    · rw [Set.uIoc_of_le hs0.le] at hx
      have hx' : dist x 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        linarith [hx.2]
      have := hball hx'
      rw [dist_eq_norm] at this
      exact this.le
  set J := ∫ τ in (0 : ℝ)..s, (T τ - 1) with hJ
  set R : X →L[𝕜] X := -(s⁻¹ • J) with hR
  have hRn : ‖R‖ < 1 := by
    rw [hR, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0)]
    calc s⁻¹ * ‖J‖ ≤ s⁻¹ * ((1 / 2) * s) := by gcongr
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have h1 : IsUnit (1 - R) := (Units.oneSub R hRn).isUnit
  have h2 : ∫ τ in (0 : ℝ)..s, T τ = algebraMap ℝ (X →L[𝕜] X) s * (1 - R) := by
    rw [hsplit, Algebra.algebraMap_eq_smul_one, hR, sub_neg_eq_add, mul_add, mul_one,
      smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  rw [h2]
  exact (IsUnit.map (algebraMap ℝ (X →L[𝕜] X)) (isUnit_iff_ne_zero.2 hs0.ne')).mul h1

/-- A uniformly continuous group is differentiable with `T' t = T t * A`. -/
lemma exists_deriv {T : ℝ → X →L[𝕜] X} (hT : HunterPDE.Semigroup.IsUniformlyContinuousGroup T) :
    ∃ A : X →L[𝕜] X, ∀ t, HasDerivAt T (T t * A) t := by
  have hc := continuous_T hT
  obtain ⟨s, hs, ⟨u, hu⟩⟩ := exists_unit hT
  set I : ℝ → X →L[𝕜] X := fun x => ∫ τ in (0 : ℝ)..x, T τ with hI
  have hId : ∀ x, HasDerivAt I (T x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hcomm : ∀ t, T t * (∫ τ in (0 : ℝ)..s, T τ) = I (t + s) - I t := by
    intro t
    have h1 : T t * (∫ τ in (0 : ℝ)..s, T τ) = ∫ τ in (0 : ℝ)..s, T t * T τ := by
      have := (ContinuousLinearMap.mul ℝ (X →L[𝕜] X) (T t)).intervalIntegral_comp_comm
        (f := T) (a := 0) (b := s) (μ := volume) (hc.intervalIntegrable _ _)
      simpa using this.symm
    rw [h1]
    have h2 : (fun τ => T t * T τ) = fun τ => T (t + τ) := by
      funext τ; rw [hT.2.1]
    rw [h2, intervalIntegral.integral_comp_add_left (fun x => T x) t]
    simp only [add_zero]
    simp only [hI]
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  refine ⟨(T s - 1) * ↑u⁻¹, fun t => ?_⟩
  have hG : HasDerivAt (fun t => I (t + s) - I t) (T (t + s) - T t) t :=
    ((hId (t + s)).comp_add_const t s).sub (hId t)
  have hfun : T = fun t => (I (t + s) - I t) * ↑u⁻¹ := by
    funext t; rw [← hcomm t, ← hu, mul_assoc, Units.mul_inv, mul_one]
  have h3 := (hG.mul_const (↑u⁻¹ : X →L[𝕜] X)).congr_of_eventuallyEq
    (Eventually.of_forall fun x => congrFun hfun x)
  refine h3.congr_deriv ?_
  rw [← hT.2.1 t s]
  noncomm_ring

/-- Solutions of `T' = T A` with `T 0 = 1` are exponentials. -/
lemma eq_exp {T : ℝ → X →L[𝕜] X} (A : X →L[𝕜] X) (h0 : T 0 = 1)
    (hd : ∀ t, HasDerivAt T (T t * A) t) (t : ℝ) :
    T t = NormedSpace.exp (t • A) := by
  set F : ℝ → X →L[𝕜] X := fun u => T u * NormedSpace.exp (u • (-A)) with hF
  have hFd : ∀ u, HasDerivAt F 0 u := by
    intro u
    have h1 := (hd u).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) u)
    refine h1.congr_deriv ?_
    noncomm_ring
  have hconst : F t = F 0 := is_const_of_deriv_eq_zero
    (fun u => (hFd u).differentiableAt) (fun u => (hFd u).deriv) t 0
  have hF0 : F 0 = 1 := by simp [hF, h0]
  have hFt : T t * NormedSpace.exp (t • (-A)) = 1 := by
    have : F t = 1 := hconst.trans hF0
    simpa [hF] using this
  have hinv : NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute, ← smul_add, neg_add_cancel, smul_zero,
      NormedSpace.exp_zero]
    exact ((Commute.refl A).neg_left.smul_left t).smul_right t
  calc T t = T t * (NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hFt, one_mul]

/-- `t ↦ exp (t • A) * B` is `C^n` for every `n`. -/
lemma contDiff_exp_mul (A : X →L[𝕜] X) :
    ∀ (n : ℕ) (B : X →L[𝕜] X), ContDiff ℝ n (fun t : ℝ => NormedSpace.exp (t • A) * B) := by
  intro n
  induction n with
  | zero =>
    intro B
    simp only [Nat.cast_zero, contDiff_zero]
    exact (continuous_iff_continuousAt.2 fun t =>
      ((hasDerivAt_exp_smul_const (𝕂 := ℝ) A t).mul_const B).continuousAt)
  | succ n ih =>
    intro B
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => ((hasDerivAt_exp_smul_const (𝕂 := ℝ) A t).mul_const B).differentiableAt,
      by simp, ?_⟩
    have : deriv (fun t : ℝ => NormedSpace.exp (t • A) * B) =
        fun t => NormedSpace.exp (t • A) * (A * B) := by
      funext t
      rw [((hasDerivAt_exp_smul_const (𝕂 := ℝ) A t).mul_const B).deriv, mul_assoc]
    rw [this]
    exact ih (A * B)

/-- The derivative of `t ↦ exp (t • A)` at `0` is `A`. -/
lemma hasDerivAt_exp_zero (A : X →L[𝕜] X) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
  have := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  simpa using this

end Aux

end UCGAux

open UCGAux in
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]
    [CompleteSpace X] (T : ℝ → X →L[𝕜] X) (hT : HunterPDE.Semigroup.IsUniformlyContinuousGroup T) :
    ContDiff ℝ ∞ T ∧
      ∃ A : X →L[𝕜] X, HasDerivAt T A 0 ∧ ∀ t : ℝ, T t = NormedSpace.exp (t • A) := by
  obtain ⟨A, hA⟩ := exists_deriv hT
  have hexp : ∀ t : ℝ, T t = NormedSpace.exp (t • A) := eq_exp A hT.1 hA
  have hfun : T = fun t : ℝ => NormedSpace.exp (t • A) := funext hexp
  refine ⟨?_, A, ?_, hexp⟩
  · rw [hfun, contDiff_infty]
    intro n
    simpa using contDiff_exp_mul A n 1
  · rw [hfun]
    exact hasDerivAt_exp_zero A
