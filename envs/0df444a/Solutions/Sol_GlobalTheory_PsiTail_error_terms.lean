-- Prove2me | solution 1 for GlobalTheory.PsiTail.error_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:03:05.975119+00:00
-- url     : https://prove2.me/submissions/a950490a-fc14-4fb4-8137-797b3f8ba2fe

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality
import Theorems.Thm_GlobalTheory_PsiTail_pow_le_exp
import Theorems.Thm_GlobalTheory_PsiTail_one_le_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.PsiTail
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory.PsiTail
theorem _root_.solution (c₁ : ℝ) (hc₁ : 0 < c₁) : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ Q u : ℝ, 3 ≤ Q → 2 ≤ u →
    (u ≤ Real.exp (Real.log Q ^ 2) → Real.log (u * Q) ^ 2 / Q ≤ K * Q ^ (-c) / Real.log u ^ 2) ∧
    (Real.exp (Real.log Q ^ 2) ≤ u →
      Real.exp (-c₁ * Real.sqrt (Real.log u)) ≤ K * Q ^ (-c) / Real.log u ^ 2) := by
  set K₁ : ℝ := (Nat.factorial 8 : ℝ) / (1 / 2) ^ 8 with hK₁
  set K₂ : ℝ := (Nat.factorial 4 : ℝ) / (c₁ / 2) ^ 4 with hK₂
  have hK₁0 : 0 < K₁ := by rw [hK₁]; positivity
  have hK₂0 : 0 < K₂ := by rw [hK₂]; positivity
  refine ⟨4 * K₁ + K₂, min (1 / 2) (c₁ / 2), by positivity, lt_min (by norm_num) (by positivity), ?_⟩
  intro Q u hQ hu
  have hQ0 : 0 < Q := by linarith
  have hu0 : 0 < u := by linarith
  have hL := one_le_log hQ
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  set L := Real.log Q with hLdef
  set c := min (1 / 2 : ℝ) (c₁ / 2) with hc
  have hQc : Q ^ (-c) = Real.exp (-(c * L)) := by
    rw [Real.rpow_def_of_pos hQ0]; congr 1; ring
  have hE : 0 < Real.exp (-(c * L)) := Real.exp_pos _
  rw [hQc]
  constructor
  · intro h
    have h1 : Real.log u ≤ L ^ 2 := by
      rw [Real.log_le_iff_le_exp hu0]; exact h
    have h2 : Real.log (u * Q) = Real.log u + L := Real.log_mul hu0.ne' hQ0.ne'
    have h3 : Real.log (u * Q) ≤ 2 * L ^ 2 := by rw [h2]; nlinarith
    have h3' : 0 ≤ Real.log (u * Q) := by rw [h2]; linarith
    have h4 : Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ 4 * L ^ 8 := by
      calc Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ (2 * L ^ 2) ^ 2 * (L ^ 2) ^ 2 := by gcongr
        _ = 4 * L ^ 8 := by ring
    have h5 : L ^ 8 ≤ K₁ * Real.exp (1 / 2 * L) := pow_le_exp (1 / 2) (by norm_num) 8 L (by linarith)
    have h6 : Real.exp (1 / 2 * L) ≤ Real.exp (-(c * L)) * Q := by
      have : Q = Real.exp L := (Real.exp_log hQ0).symm
      conv_rhs => rw [this]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : c ≤ 1 / 2 := min_le_left _ _
      nlinarith
    rw [div_le_div_iff₀ hQ0 (by positivity)]
    have h7 : K₁ * Real.exp (1 / 2 * L) ≤ K₁ * (Real.exp (-(c * L)) * Q) := by gcongr
    have h8 : 0 ≤ K₂ * (Real.exp (-(c * L)) * Q) := by positivity
    calc Real.log (u * Q) ^ 2 * Real.log u ^ 2 ≤ 4 * L ^ 8 := h4
      _ ≤ 4 * (K₁ * (Real.exp (-(c * L)) * Q)) + K₂ * (Real.exp (-(c * L)) * Q) := by
        have := h5.trans h7
        linarith
      _ = _ := by ring
  · intro h
    have h1 : L ^ 2 ≤ Real.log u := by
      rw [Real.le_log_iff_exp_le hu0]; exact h
    set s := Real.sqrt (Real.log u) with hs
    have hs2 : s ^ 2 = Real.log u := Real.sq_sqrt hlu.le
    have hLs : L ≤ s := Real.le_sqrt_of_sq_le h1
    have h5 : s ^ 4 ≤ K₂ * Real.exp (c₁ / 2 * s) := pow_le_exp (c₁ / 2) (by positivity) 4 s (by linarith)
    have h6 : Real.exp (-c₁ * s) * Real.exp (c₁ / 2 * s) ≤ Real.exp (-(c * L)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h7 : c ≤ c₁ / 2 := min_le_right _ _
      have h8 : c * L ≤ c₁ / 2 * s := by gcongr
      linarith
    rw [le_div_iff₀ (by positivity), ← hs2]
    calc Real.exp (-c₁ * s) * (s ^ 2) ^ 2 = Real.exp (-c₁ * s) * s ^ 4 := by ring
      _ ≤ Real.exp (-c₁ * s) * (K₂ * Real.exp (c₁ / 2 * s)) := by gcongr
      _ = K₂ * (Real.exp (-c₁ * s) * Real.exp (c₁ / 2 * s)) := by ring
      _ ≤ K₂ * Real.exp (-(c * L)) := by gcongr
      _ ≤ (4 * K₁ + K₂) * Real.exp (-(c * L)) := by gcongr; linarith
end GlobalTheory.PsiTail
