-- Prove2me | solution 1 for GlobalTheory.T.frobenius_polydisc_windows_surjective_bounds_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:23.599589+00:00
-- url     : https://prove2.me/submissions/fef42f70-281f-4199-b053-5b7c4147b752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPolydiscWindowsSurjectiveBoundsZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPolydiscWindowsSurjectiveBoundsZeroStatement
import Theorems.Thm_GlobalTheory_PMonE_winThm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : WinThm := by
  first | exact @GlobalTheory.PMonE.winThm | exact GlobalTheory.PMonE.winThm | (intros; apply GlobalTheory.PMonE.winThm <;> assumption)
end _root_.GlobalTheory.T
