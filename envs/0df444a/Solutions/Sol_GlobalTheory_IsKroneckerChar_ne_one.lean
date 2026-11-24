-- Prove2me | solution 1 for GlobalTheory.IsKroneckerChar.ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:07:01.756243+00:00
-- url     : https://prove2.me/submissions/48612416-28fa-4c30-bf95-b107ffbfd9cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Theorems.Thm_GlobalTheory_IsKroneckerChar_apply_neg_one

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
open GlobalTheory.IsKroneckerChar
variable {d : ℕ} {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ)
include hχ
namespace GlobalTheory.IsKroneckerChar
theorem _root_.solution (hd : 0 < d) : χ ≠ 1 := fun h => by
  have := hχ.apply_neg_one hd
  rw [h, MulChar.one_apply isUnit_one.neg] at this
  norm_num at this
end GlobalTheory.IsKroneckerChar
