-- Prove2me | solution 1 for N4Code.dRow_eq_mInd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:05.459154+00:00
-- url     : https://prove2.me/submissions/a4e6e600-1344-42bc-a0f2-7a03bf8ee009

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_dRow_eq_indicator_sum


set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (j : Fin 4) (w : Word n) :
    dRow C j w = ∑ u : Fin n, mInd C j w u := by
  rw [dRow_eq_indicator_sum]
  rfl
end N4Code
