-- Prove2me | solution 1 for LoanInsurance.Liquid.b3_lamTildeL
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:06:34.496279+00:00
-- url     : https://prove2.me/submissions/2b3d948c-1e74-4f0d-a7c7-c29b3e1bbd4d

import Mathlib
import Definitions.Def_LoanInsurance_Liquid_Model
set_option autoImplicit false
open LoanInsurance.Liquid

theorem solution (P : Params) (hP : P.Standing) :
    (P.A ≤ P.lam * P.pUStar ↔
        0 ≤ P.μ * P.ν * P.lam ^ 2 - P.ν * P.lam - (1 - P.μ) * (1 - P.ν)) ∧
      (0 ≤ P.μ * P.ν * P.lam ^ 2 - P.ν * P.lam - (1 - P.μ) * (1 - P.ν) ↔
        P.lamTildeL ≤ P.lam) := by
  obtain ⟨hA, hμ, hμψ, hψ1, hν, hν1, hlam, -⟩ := hP
  have hDp : 0 < P.Dp := by
    unfold Params.Dp
    have : 0 < (1 - P.ν) * (1 - P.μ) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_pos hν (by linarith : (0:ℝ) < P.lam)]
  refine ⟨?_, ?_⟩
  · unfold Params.pUStar
    have e : P.lam * (P.ν * P.lam * P.μ * P.A / P.Dp) = P.ν * P.lam ^ 2 * P.μ * P.A / P.Dp := by ring
    rw [e, le_div_iff₀ hDp]
    unfold Params.Dp
    constructor
    · intro h
      have : P.A * (P.ν * P.lam + (1 - P.ν) * (1 - P.μ)) ≤ P.A * (P.ν * P.lam ^ 2 * P.μ) := by nlinarith
      have := le_of_mul_le_mul_left this hA
      nlinarith
    · intro h
      have : P.A * (P.ν * P.lam + (1 - P.ν) * (1 - P.μ)) ≤ P.A * (P.ν * P.lam ^ 2 * P.μ) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hA.le
      nlinarith
  · unfold Params.lamTildeL
    set s := Real.sqrt (1 / (4 * P.μ ^ 2) + (1 - P.μ) * (1 - P.ν) / (P.μ * P.ν)) with hs
    have hnn : 0 ≤ 1 / (4 * P.μ ^ 2) + (1 - P.μ) * (1 - P.ν) / (P.μ * P.ν) := by
      have : 0 ≤ (1 - P.μ) * (1 - P.ν) / (P.μ * P.ν) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      positivity
    have hs2 : s ^ 2 = 1 / (4 * P.μ ^ 2) + (1 - P.μ) * (1 - P.ν) / (P.μ * P.ν) := Real.sq_sqrt hnn
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs1 : 1 / (2 * P.μ) ≤ s := by
      by_contra hc
      push_neg at hc
      have h1 : s ^ 2 < (1 / (2 * P.μ)) ^ 2 := by nlinarith
      have h2 : (1 / (2 * P.μ)) ^ 2 = 1 / (4 * P.μ ^ 2) := by field_simp; ring
      have : 0 ≤ (1 - P.μ) * (1 - P.ν) / (P.μ * P.ν) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      linarith
    have key : P.μ * P.ν * P.lam ^ 2 - P.ν * P.lam - (1 - P.μ) * (1 - P.ν)
        = P.μ * P.ν * ((P.lam - 1 / (2 * P.μ)) ^ 2 - s ^ 2) := by
      rw [hs2]; field_simp; ring
    rw [key]
    have hμν : 0 < P.μ * P.ν := mul_pos hμ hν
    have hpos : 0 < 1 / (2 * P.μ) := by positivity
    constructor
    · intro h
      have h' : 0 ≤ (P.lam - 1 / (2 * P.μ)) ^ 2 - s ^ 2 := by
        by_contra hc; push_neg at hc; nlinarith
      by_contra hc
      push_neg at hc
      have : P.lam - 1 / (2 * P.μ) < s := by linarith
      have : -s < P.lam - 1 / (2 * P.μ) := by linarith
      nlinarith
    · intro h
      apply mul_nonneg hμν.le
      nlinarith
