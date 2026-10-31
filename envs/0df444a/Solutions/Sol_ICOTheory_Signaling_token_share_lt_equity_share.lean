-- Prove2me | solution 1 for ICOTheory.Signaling.token_share_lt_equity_share
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:54:02.323138+00:00
-- url     : https://prove2.me/submissions/179538b1-b121-4a94-9b76-3c83745e0b2f

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaBarT
import Definitions.Def_ICOTheory_Signaling_alphaBarE
open ICOTheory.Signaling

theorem solution{I C μ : ℝ} (hI : 0 < I) (hC : 0 < C) (hCμ : C < μ / 4) :
    alphaBarT I μ < alphaBarE I C μ := by
  unfold alphaBarT alphaBarE
  apply div_lt_div_of_pos_left hI (by linarith) (by linarith)
