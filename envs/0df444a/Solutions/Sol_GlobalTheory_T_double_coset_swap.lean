-- Prove2me | solution 1 for GlobalTheory.T.double_coset_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:40.623372+00:00
-- url     : https://prove2.me/submissions/9a4d3248-924e-4651-81c1-07fedba06e28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwapStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_dosetSwap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : DosetSwap := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.dosetSwap | exact GlobalTheory.CompanionTheory.InertZeta.dosetSwap | (intros; apply GlobalTheory.CompanionTheory.InertZeta.dosetSwap <;> assumption)
end _root_.GlobalTheory.T
