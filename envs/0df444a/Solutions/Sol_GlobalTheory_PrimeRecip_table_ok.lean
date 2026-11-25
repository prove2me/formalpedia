-- Prove2me | solution 1 for GlobalTheory.PrimeRecip.table_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:16.058718+00:00
-- url     : https://prove2.me/submissions/aa2f95d1-af55-427a-acbb-f306010324be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvFiveLogLeSumInvPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open GlobalTheory GlobalTheory.PrimeRecip
namespace GlobalTheory.PrimeRecip
theorem _root_.solution : okAll 100 table 16900 = true := by decide +kernel
end GlobalTheory.PrimeRecip
