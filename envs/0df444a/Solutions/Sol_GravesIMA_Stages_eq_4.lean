-- Prove2me | solution 1 for GravesIMA.Stages.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:39:39.969971+00:00
-- url     : https://prove2.me/submissions/63af5678-362f-4897-946b-139f50909742

import Mathlib
import Definitions.Def_GravesIMA_Stages_Model

set_option autoImplicit false
open GravesIMA.Stages

theorem solution (μ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (L : ℕ) (ε d F q x : ℤ → ℝ)
    (h : IsStage μ α L ε d F q x) (t : ℤ) (ht : 1 ≤ t) :
    d t - F t = ε t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  induction t, ht using Int.le_induction with
  | base => rw [h1, h3]; ring
  | succ t ht ih =>
    have h2' := h2 (t + 1) (by omega)
    simp only [add_sub_cancel_right] at h2'
    have hd : d t = F t + ε t := by linarith
    rw [h2', h4 t ht, hd]; ring
