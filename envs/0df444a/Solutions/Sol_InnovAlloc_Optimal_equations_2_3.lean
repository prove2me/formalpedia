-- Prove2me | solution 1 for InnovAlloc.Optimal.equations_2_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:46:39.891331+00:00
-- url     : https://prove2.me/submissions/5fafc9fe-1ac1-446f-ba89-09e3f341805b

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model
set_option autoImplicit false
open InnovAlloc.Optimal

theorem ww_succ_star (γ b : ℝ) (hγ : 0 < γ) (hb : 0 < b) :
    succ b (effortStar γ b) = (if γ * b ≤ 1 then 0 else 1 - 1 / (γ * b)) := by
  unfold succ effortStar
  by_cases hs : γ * b < 1
  · rw [if_pos hs, if_pos hs.le]
    simp
  · push_neg at hs
    rw [if_neg (not_lt.2 hs)]
    have hpos : 0 < γ * b := by positivity
    have e : -(b * (Real.log (γ * b) / b)) = -Real.log (γ * b) := by
      field_simp
    rw [e, Real.exp_neg, Real.exp_log hpos]
    by_cases h1 : γ * b ≤ 1
    · have : γ * b = 1 := le_antisymm h1 hs
      rw [if_pos h1, this]; norm_num
    · rw [if_neg h1]
      field_simp

theorem solution (γ b : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) (hb : 0 < b) :
    (∀ x : ℝ, 0 ≤ x →
      ((∀ z : ℝ, 0 ≤ z → γ * succ b z - z ≤ γ * succ b x - x) ↔
        x = effortStar γ b)) ∧
    succ b (effortStar γ b) =
      (if γ * b ≤ 1 then 0 else 1 - 1 / (γ * b)) ∧
    MonotoneOn (fun t : ℝ => succ t (effortStar γ t)) (Set.Ioi 0) := by
  have hF : ∀ z : ℝ, γ * succ b z - z = γ * (1 - Real.exp (-(b * z))) - z := by
    intro z; unfold succ; ring
  refine ⟨?_, ww_succ_star γ b hγ hb, ?_⟩
  · intro x hx
    by_cases hs : γ * b < 1
    · have hx0 : effortStar γ b = 0 := by unfold effortStar; rw [if_pos hs]
      rw [hx0]
      -- f(z) ≤ (γ b - 1) z ≤ 0 with equality only at 0
      have hle : ∀ z : ℝ, 0 ≤ z → γ * succ b z - z ≤ (γ * b - 1) * z := by
        intro z hz
        rw [hF]
        have := Real.add_one_le_exp (-(b * z))
        nlinarith
      constructor
      · intro h
        by_contra hne
        have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
        have h0 := h 0 le_rfl
        have h1 := hle x hx
        have h2 : γ * succ b 0 - 0 = 0 := by unfold succ; simp
        have h3 : (γ * b - 1) * x < 0 := mul_neg_of_neg_of_pos (by linarith) hxpos
        linarith
      · intro h z hz
        rw [h]
        have h2 : γ * succ b 0 - 0 = 0 := by unfold succ; simp
        rw [h2]
        have := hle z hz
        nlinarith
    · push_neg at hs
      have hpos : 0 < γ * b := by positivity
      have hx0 : effortStar γ b = Real.log (γ * b) / b := by
        unfold effortStar; rw [if_neg (not_lt.2 hs)]
      rw [hx0]
      have key : ∀ z : ℝ, γ * succ b z - z - (γ * succ b (Real.log (γ * b) / b) - Real.log (γ * b) / b)
          = (1 / b) * (1 + (Real.log (γ * b) - b * z) - Real.exp (Real.log (γ * b) - b * z)) := by
        intro z
        rw [hF, hF]
        have e1 : Real.exp (-(b * z)) = Real.exp (Real.log (γ * b) - b * z) / (γ * b) := by
          rw [Real.exp_sub, Real.exp_log hpos, Real.exp_neg]
          field_simp
        have e2 : Real.exp (-(b * (Real.log (γ * b) / b))) = 1 / (γ * b) := by
          have : -(b * (Real.log (γ * b) / b)) = -Real.log (γ * b) := by field_simp
          rw [this, Real.exp_neg, Real.exp_log hpos]
          simp
        rw [e1, e2]
        field_simp
        ring
      constructor
      · intro h
        by_contra hne
        have hxne : b * x - Real.log (γ * b) ≠ 0 := by
          intro h0
          apply hne
          field_simp
          linarith
        have hlt := Real.add_one_lt_exp (show Real.log (γ * b) - b * x ≠ 0 by
          intro h0; apply hxne; linarith)
        have hk := key (Real.log (γ * b) / b)
        have hk2 := key x
        have hh := h (Real.log (γ * b) / b) (by
          apply div_nonneg _ hb.le
          exact Real.log_nonneg hs)
        have : (1 / b) * (1 + (Real.log (γ * b) - b * x) - Real.exp (Real.log (γ * b) - b * x)) < 0 := by
          apply mul_neg_of_pos_of_neg (by positivity)
          linarith
        linarith
      · intro h z hz
        rw [h]
        have := key z
        have hle := Real.add_one_le_exp (Real.log (γ * b) - b * z)
        have : (1 / b) * (1 + (Real.log (γ * b) - b * z) - Real.exp (Real.log (γ * b) - b * z)) ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
          linarith
        linarith
  · intro s hs t ht hst
    simp only [Set.mem_Ioi] at hs ht
    show succ s (effortStar γ s) ≤ succ t (effortStar γ t)
    rw [ww_succ_star γ s hγ hs, ww_succ_star γ t hγ ht]
    have hγst : γ * s ≤ γ * t := by nlinarith
    split_ifs with h1 h2 h2
    · exact le_rfl
    · have h3 : 1 / (γ * t) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    · exfalso; linarith
    · have : 1 / (γ * t) ≤ 1 / (γ * s) := by
        apply one_div_le_one_div_of_le (by positivity) hγst
      linarith
