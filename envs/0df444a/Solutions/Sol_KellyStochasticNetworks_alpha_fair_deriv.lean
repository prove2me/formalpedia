-- Prove2me | solution 1 for KellyStochasticNetworks.alpha_fair_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:13:19.065559+00:00
-- url     : https://prove2.me/submissions/58e21630-9874-4496-832b-a800090d9128

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

lemma af_obj_eq {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (X : Fin R → ℝ) :
    alphaFairObjective w n α X =
      ∑ r, w r * n r ^ α * (if α = 1 then Real.log (X r) else X r ^ (1 - α) / (1 - α)) := by
  by_cases h : α = 1
  · subst h; simp [alphaFairObjective]
  · simp [alphaFairObjective, h]

lemma af_phi_deriv {α u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => if α = 1 then Real.log t else t ^ (1 - α) / (1 - α))
      (u ^ (-α)) u := by
  by_cases h : α = 1
  · subst h
    simp only [if_true]
    rw [Real.rpow_neg_one]
    exact Real.hasDerivAt_log hu.ne'
  · simp only [h, if_false]
    have hp0 : (1 - α) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hd := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hu.ne')).div_const (1 - α)
    have e : (1 - α) * u ^ (1 - α - 1) / (1 - α) = u ^ (-α) := by
      rw [show (1:ℝ) - α - 1 = -α by ring]; field_simp
    rw [e] at hd
    exact hd

theorem af_deriv {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) (X : Fin R → ℝ) (hX : ∀ r, 0 < X r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => alphaFairObjective w n α (Function.update X r t))
      (w r * n r ^ α * X r ^ (-α)) (X r) := by
  have hfun : (fun t => alphaFairObjective w n α (Function.update X r t)) =
      fun t => ∑ r', w r' * n r' ^ α * (if α = 1 then Real.log (Function.update X r t r')
        else Function.update X r t r' ^ (1 - α) / (1 - α)) := by
    funext t; exact af_obj_eq w n α _
  rw [hfun]
  have hd : ∀ r' ∈ Finset.univ, HasDerivAt (fun t => w r' * n r' ^ α *
      (if α = 1 then Real.log (Function.update X r t r')
        else Function.update X r t r' ^ (1 - α) / (1 - α)))
      (if r' = r then w r * n r ^ α * X r ^ (-α) else 0) (X r) := by
    intro r' _
    by_cases hr : r' = r
    · subst hr
      simp only [Function.update_self, if_true]
      exact (af_phi_deriv (hX r')).const_mul _
    · simp only [Function.update_of_ne hr, hr, if_false]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum hd
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) (X : Fin R → ℝ) (hX : ∀ r, 0 < X r) (r : Fin R) :
    HasDerivAt (fun t : ℝ => alphaFairObjective w n α (Function.update X r t))
      (w r * n r ^ α * X r ^ (-α)) (X r) := by
  exact af_deriv w n α hα hw hn X hX r
