-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_clause_gain_continuous
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:33:09.192956+00:00
-- url     : https://prove2.me/submissions/3d12ff4d-852e-489a-b9ad-cc5430e54745

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClause
import Mathlib
set_option autoImplicit false
open KSATSingleFlip.Connect Set

theorem solution (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc 0 1))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    ContinuousOn (softClauseGain ψ v0 v1) (Icc 0 1) := by
  have hzleft (v : ℝ) : softPerspective ψ 0 v = 0 := by
    by_cases hv : v=0
    · simp [softPerspective,hv]
    · simp [softPerspective,hv,hψ1]
  have hzright (v : ℝ) : softPerspective ψ v 0 = 0 := by simp [softPerspective,hψ0]
  by_cases h0 : v0=0
  · subst v0
    have hh : softClauseGain ψ 0 v1 = fun _ => 0 := by funext s; simp [softClauseGain,hzleft]
    rw [hh]
    exact continuousOn_const
  by_cases h1 : v1=0
  · subst v1
    have hh : softClauseGain ψ v0 0 = fun _ => 0 := by funext s; simp [softClauseGain,hzright]
    rw [hh]
    exact continuousOn_const
  have hv0p : 0 < v0 := lt_of_le_of_ne hv0 (Ne.symm h0)
  have hv1p : 0 < v1 := lt_of_le_of_ne hv1 (Ne.symm h1)
  let A : ℝ → ℝ := fun s => (1-s)*v0+v1
  let B : ℝ → ℝ := fun s => v0+(1-s)*v1
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hApos (s : ℝ) (hs : s ∈ Icc 0 1) : 0 < A s := by
    dsimp [A]
    have : 0 ≤ (1-s)*v0 := mul_nonneg (by linarith [hs.2]) hv0
    linarith
  have hBpos (s : ℝ) (hs : s ∈ Icc 0 1) : 0 < B s := by
    dsimp [B]
    have : 0 ≤ (1-s)*v1 := mul_nonneg (by linarith [hs.2]) hv1
    linarith
  have hargA : ContinuousOn (fun s => v1 / A s) (Icc 0 1) :=
    continuousOn_const.div hA.continuousOn (fun s hs => ne_of_gt (hApos s hs))
  have hargB : ContinuousOn (fun s => ((1-s)*v1) / B s) (Icc 0 1) := by
    apply ContinuousOn.div _ hB.continuousOn (fun s hs => ne_of_gt (hBpos s hs))
    fun_prop
  have hmapA : MapsTo (fun s => v1/A s) (Icc 0 1) (Icc 0 1) := by
    intro s hs
    constructor
    · exact div_nonneg hv1 (le_of_lt (hApos s hs))
    · apply (div_le_one₀ (hApos s hs)).2
      dsimp [A]
      have : 0 ≤ (1-s)*v0 := mul_nonneg (by linarith [hs.2]) hv0
      linarith
  have hmapB : MapsTo (fun s => ((1-s)*v1)/B s) (Icc 0 1) (Icc 0 1) := by
    intro s hs
    constructor
    · apply div_nonneg _ (le_of_lt (hBpos s hs))
      exact mul_nonneg (by linarith [hs.2]) hv1
    · apply (div_le_one₀ (hBpos s hs)).2
      dsimp [B]
      linarith
  have hpA : ContinuousOn (fun s => softPerspective ψ ((1-s)*v0) v1) (Icc 0 1) := by
    have hh := hA.continuousOn.mul (hψ.comp hargA hmapA)
    change ContinuousOn (fun s => A s * ψ (v1/A s)) (Icc 0 1) at hh
    exact hh
  have hpB : ContinuousOn (fun s => softPerspective ψ v0 ((1-s)*v1)) (Icc 0 1) := by
    have hh := hB.continuousOn.mul (hψ.comp hargB hmapB)
    change ContinuousOn (fun s => B s * ψ (((1-s)*v1)/B s)) (Icc 0 1) at hh
    exact hh
  have hpconst : ContinuousOn (fun s : ℝ => (1-s)*softPerspective ψ v0 v1) (Icc 0 1) := by fun_prop
  unfold softClauseGain
  exact ((hpA.add hpB).div_const 2).sub hpconst
