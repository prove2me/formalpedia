-- Prove2me | solution 1 for MatchCongestion.Welfare.indifference_p628
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:21:40.285993+00:00
-- url     : https://prove2.me/submissions/26f5d3a4-627f-4fe0-b935-115edd8d9c03

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp : P.ca < p) :
    E (Mbr P p * p) = csp P ↔ Eq14 P p := by
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
  have hlog : Real.log (P.ca / p) = - L := by
    rw [hL, ← inv_div, Real.log_inv]
  have hE : E (Mbr P p * p) = (1 - P.ca / p) / L := by
    unfold E
    rw [if_neg (by rw [hmp]; exact hLpos.ne'), hexp, hmp]
  rw [hE]
  unfold Eq14 csp
  rw [hlog]
  rw [div_eq_iff hLpos.ne']
  constructor
  · intro h
    have : P.cs / P.β * L = 1 - P.ca / p := by rw [← h]
    linarith
  · intro h
    linarith
