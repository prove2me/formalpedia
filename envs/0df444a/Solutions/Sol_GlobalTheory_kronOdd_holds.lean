-- Prove2me | solution 1 for GlobalTheory.kronOdd_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:44.157808+00:00
-- url     : https://prove2.me/submissions/de6d7469-d774-4bc8-83b6-7d8b5e37d149

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JacobiSymNegEqOfThreeModFour
import Theorems.Thm_GlobalTheory_jacobiSym_neg_eq_of_three_mod_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.KronOdd :=
  fun q n hq hn => jacobiSym_neg_eq_of_three_mod_four q n hq hn
end GlobalTheory
