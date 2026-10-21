-- Prove2me | solution 1 for MatchCongestion.Welfare.endnote_12_eq16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:17:30.562533+00:00
-- url     : https://prove2.me/submissions/cd768e8e-9ca6-44da-b282-da835fe6d659

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem solution (P : Params) (hP : P.Standing) (m α p q : ℝ)
    (hss : IsMFSS P m α p q) (hm : m = Mbr P p) (hp : P.ca < p) :
    We P α m q = P.r * (1 - P.ca / p + P.cs / P.β * Real.log (P.ca / p)) := by
  obtain ⟨_, hr, hβ, _, hca, _⟩ := hP
  obtain ⟨hq, hpe⟩ := hss
  have hp0 : 0 < p := hca.trans hp
  have hpc : 1 < p / P.ca := by rw [lt_div_iff₀ hca]; linarith
  set L := Real.log (p / P.ca) with hL
  have hLpos : 0 < L := Real.log_pos hpc
  have hM : m = (1 / p) * L := by
    rw [hm]; unfold Mbr; rw [if_neg (not_le.mpr hp)]
  have hmp : m * p = L := by rw [hM]; field_simp
  have hmpos : 0 < m := by rw [hM]; positivity
  have hexp : Real.exp (-(m * p)) = P.ca / p := by
    rw [hmp, hL, Real.exp_neg, Real.exp_log (by linarith), inv_div]
  have hlog : Real.log (P.ca / p) = - L := by
    rw [hL, ← inv_div, Real.log_inv]
  have h1 : 0 < 1 - P.ca / p := by
    rw [sub_pos, div_lt_one hp0]; exact hp
  have hq' : q = (1 - P.ca / p) / L := by
    rw [hq]; unfold E
    rw [if_neg (by rw [hmp]; exact hLpos.ne'), hexp, hmp]
  have hqpos : 0 < q := by rw [hq']; positivity
  have hLq : L * q = 1 - P.ca / p := by rw [hq']; field_simp
  set x := P.r * m * P.β * q with hx
  have hxpos : 0 < x := by positivity
  have hpe' : p = α * P.β * ((1 - Real.exp (-x)) / x) := by
    rw [hpe]; unfold E; rw [if_neg hxpos.ne']
  have hA : α * (1 - Real.exp (-x)) = P.r * L * q := by
    have : α * (1 - Real.exp (-x)) * P.β = p * x := by
      rw [hpe']; field_simp
    have h2 : p * x = P.β * (P.r * L * q) := by
      rw [hx, ← hmp]; ring
    have : α * (1 - Real.exp (-x)) * P.β = (P.r * L * q) * P.β := by
      rw [this, h2]; ring
    exact mul_right_cancel₀ hβ.ne' this
  unfold We csp
  rw [hA, hlog]
  have : P.r * L * q * (1 - P.cs / P.β / q) = P.r * (L * q) - P.r * (P.cs / P.β) * L := by
    field_simp
  rw [this, hLq]
  ring
