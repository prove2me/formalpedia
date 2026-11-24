-- Prove2me | solution 1 for GlobalTheory.isKroneckerChar_quadraticChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:44.679821+00:00
-- url     : https://prove2.me/submissions/204f62b8-86b2-4211-955c-60d6fdc502f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_isKroneckerChar_of_jacobiSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory
open QuadraticZeta
namespace GlobalTheory
theorem _root_.solution {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3) :
    IsKroneckerChar ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) :=
  isKroneckerChar_of_jacobiSym hd fun n => by
    simp [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
end GlobalTheory
