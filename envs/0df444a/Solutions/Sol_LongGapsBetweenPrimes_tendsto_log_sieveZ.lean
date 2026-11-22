-- Prove2me | solution 1 for LongGapsBetweenPrimes.tendsto_log_sieveZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:40:55.972003+00:00
-- url     : https://prove2.me/submissions/f4bfdc04-0574-4bcc-a451-71c466543839

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tendsto_sieveZ

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution :
    Filter.Tendsto (fun x : ℝ => Real.log (sieveZ x)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_sieveZ)
end LongGapsBetweenPrimes
