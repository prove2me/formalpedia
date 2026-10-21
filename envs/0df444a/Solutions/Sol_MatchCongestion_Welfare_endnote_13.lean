-- Prove2me | solution 1 for MatchCongestion.Welfare.endnote_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:20:18.946003+00:00
-- url     : https://prove2.me/submissions/18195d8d-45b0-4c60-ad32-64245bc9666f

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp : P.ca < p) :
    (1 - Real.exp (-(Mbr P p * p)) = 1 - P.ca / p) ∧
    (1 - Real.exp (-(P.r * Mbr P p * P.β * E (Mbr P p * p))) =
      1 - Real.exp (-(P.r * P.β / p) * (1 - P.ca / p))) ∧
    (p = 1 * P.β * E (P.r * Mbr P p * P.β * E (Mbr P p * p)) ↔ Eq13 P p) := by
  obtain ⟨_, hr, hβ, _, hca, _⟩ := hP
  have hp0 : 0 < p := hca.trans hp
  have hpc : 1 < p / P.ca := by rw [lt_div_iff₀ hca]; linarith
  set L := Real.log (p / P.ca) with hL
  have hLpos : 0 < L := Real.log_pos hpc
  have hM : Mbr P p = (1 / p) * L := by
    unfold Mbr; rw [if_neg (not_le.mpr hp)]
  have hmp : Mbr P p * p = L := by rw [hM]; field_simp
  have hexp : Real.exp (-(Mbr P p * p)) = P.ca / p := by
    rw [hmp, hL, Real.exp_neg, Real.exp_log (by linarith), inv_div]
  have h1 : 0 < 1 - P.ca / p := by
    rw [sub_pos, div_lt_one hp0]; exact hp
  have hE : E (Mbr P p * p) = (1 - P.ca / p) / L := by
    unfold E
    rw [if_neg (by rw [hmp]; exact hLpos.ne'), hexp, hmp]
  have hy : P.r * Mbr P p * P.β * E (Mbr P p * p) = P.r * P.β / p * (1 - P.ca / p) := by
    rw [hE, hM]; field_simp
  have hypos : 0 < P.r * P.β / p * (1 - P.ca / p) := by positivity
  refine ⟨by rw [hexp], ?_, ?_⟩
  · rw [hy]; congr 3; ring
  · rw [hy]
    unfold E Eq13
    rw [if_neg hypos.ne']
    have e : -(P.r * P.β / p) * (1 - P.ca / p) = -(P.r * P.β / p * (1 - P.ca / p)) := by ring
    rw [e]
    set y := P.r * P.β / p * (1 - P.ca / p) with hyd
    have hpy : p * y = P.β * (P.r * (1 - P.ca / p)) := by rw [hyd]; field_simp
    constructor
    · intro h
      have : p * y = P.β * (1 - Real.exp (-y)) := by
        rw [h]; field_simp
      have h3 : P.β * (P.r * (1 - P.ca / p)) = P.β * (1 - Real.exp (-y)) := by rw [← hpy, this]
      exact mul_left_cancel₀ hβ.ne' h3
    · intro h
      have h' : 1 - Real.exp (-y) = P.r * (1 - P.ca / p) := h.symm
      rw [h']
      have hy0 : y ≠ 0 := hypos.ne'
      rw [one_mul, ← mul_div_assoc, eq_div_iff hy0]
      exact hpy
