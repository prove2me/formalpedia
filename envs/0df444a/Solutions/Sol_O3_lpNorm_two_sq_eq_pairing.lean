-- Prove2me | solution 1 for O3.lpNorm_two_sq_eq_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:30.45313+00:00
-- url     : https://prove2.me/submissions/db3fffce-4e77-4fa8-b853-9140a5199fbd

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
import Theorems.Thm_O3_Stage2RouteC_lpNorm_two_sq


set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d : ℕ} (x : Vec d) :
    (lpNorm 2 x) ^ (2 : ℕ) = pairing x x := by
  rw [Stage2RouteC.lpNorm_two_sq]
  unfold pairing
  apply Finset.sum_congr rfl
  intro i _
  ring
end O3
