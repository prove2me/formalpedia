-- Prove2me | solution 1 for HryniewiczCriterion.czIndexOfPath_ge_three_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T22:17:41.996672+00:00
-- url     : https://prove2.me/submissions/27a3308c-de36-484a-8245-76b032dce4bd

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

open HryniewiczCriterion Set
set_option autoImplicit false

theorem solution (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ)
    (hab : a ≤ b) (hw : windingInterval φ = Set.Icc a b) (hwidth : b - a < 1) :
    3 ≤ czIndexOfPath φ ↔ ∀ d ∈ windingInterval φ, 1 < d := by
  have ha : sInf (windingInterval φ) = a := by rw [hw]; exact csInf_Icc hab
  have hb : sSup (windingInterval φ) = b := by rw [hw]; exact csSup_Icc hab
  have he : (∀ d ∈ windingInterval φ, 1 < d) ↔ 1 < a := by
    rw [hw]
    constructor
    · intro h
      exact h a ⟨le_rfl, hab⟩
    · intro h d hd
      exact h.trans_le hd.1
  rw [he]
  unfold czIndexOfPath
  rw [ha, hb]
  dsimp only
  constructor
  · intro h
    by_contra hn
    have hal : a ≤ 1 := le_of_not_gt hn
    have hbl : b ≤ (2 : ℤ) := by norm_num; linarith
    have hn2 : Int.ceil b ≤ 2 := Int.ceil_le.mpr hbl
    split_ifs at h with hc
    · omega
    · have hn1 : Int.ceil b ≤ 1 := by
        by_contra hn1
        have hn_eq : Int.ceil b = 2 := by omega
        rw [hn_eq] at hc
        norm_num at hc
        linarith
      omega
  · intro h
    have hn : (1 : ℤ) < Int.ceil b := Int.lt_ceil.mpr (by simpa using h.trans_le hab)
    split_ifs with hc
    · have hr : (2 : ℝ) < (Int.ceil b : ℝ) := by
        push_cast at hc
        linarith
      have hn3 : (2 : ℤ) < Int.ceil b := by exact_mod_cast hr
      omega
    · omega

