-- Prove2me | solution 1 for MatchCongestion.Welfare.endnote_12_eq15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:16:04.436005+00:00
-- url     : https://prove2.me/submissions/ee18c81b-8c13-4151-975b-b964d35605bb

import Mathlib
import Definitions.Def_MatchCongestion_Welfare_Setting

set_option autoImplicit false
open MatchCongestion.Welfare

theorem solution (P : Params) (hca : 0 < P.ca) (p : ℝ) (hp : P.ca < p) :
    Wa P (Mbr P p) p = 1 - P.ca / p + P.ca / p * Real.log (P.ca / p) := by
  have hp0 : 0 < p := hca.trans hp
  have hM : Mbr P p = (1 / p) * Real.log (p / P.ca) := by
    unfold Mbr; rw [if_neg (not_le.mpr hp)]
  have hmp : Mbr P p * p = Real.log (p / P.ca) := by
    rw [hM]; field_simp
  have hpc : 0 < p / P.ca := div_pos hp0 hca
  have hexp : Real.exp (-(Mbr P p * p)) = P.ca / p := by
    rw [hmp, Real.exp_neg, Real.exp_log hpc, inv_div]
  have hlog : Real.log (P.ca / p) = - Real.log (p / P.ca) := by
    rw [← inv_div, Real.log_inv]
  unfold Wa
  rw [hexp, hM, hlog]
  field_simp
  ring
