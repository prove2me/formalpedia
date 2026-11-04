-- Prove2me | solution 1 for Light.powTable_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:05.989061+00:00
-- url     : https://prove2.me/submissions/4f2845eb-b7d2-485d-ba38-c69cb94082fe

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Mathlib.Data.Int.SuccPred
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_WeightedCache3SUM_Alias_4836f77abf95e256
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros


set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open PowTable
namespace Light
theorem _root_.solution {p : ℕ} (hp : P[p]? = some powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(dst : ℤ), L, b] μ (powTableTime L) fun _ μ' =>
      Seg μ' dst (powList b L) ∧ SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  .of_body hp (frame_append_zeros [(dst : ℤ), L, b] 2 ▸ powTable_ends 0 0 [] hw hdst hpow)
end Light
